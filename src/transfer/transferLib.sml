structure transferLib :> transferLib =
struct

open HolKernel boolLib
open transferTheory FullUnify simpLib
open pred_setTheory

val op $ = Portable.$
infix ++ |> ~> +++

type config = {cleftp:bool,force_imp:bool,hints:string list}

val equalityp_tm = prim_mk_const{Name = "equalityp", Thy = "transfer"}
val right_unique_tm = prim_mk_const{Name = "right_unique", Thy = "transfer"}
val cimp_tm = mk_icomb(combinSyntax.C_tm, boolSyntax.implication)

val numeral_pattern = mk_comb(numSyntax.numeral_tm, mk_var("n", numSyntax.num))

val SIMP_CONV = simpLib.SIMP_CONV
val SIMP_RULE = simpLib.SIMP_RULE

val transfer_ss = boolSimps.bool_ss ++ combinSimps.COMBIN_ss ++
                  rewrites [eq_equalityp, pairTheory.UNCURRY_DEF, surj_EQ,
                            right_unique_EQ, left_unique_EQ, total_EQ]

fun relconstraint_tm t =
    case dest_term t of
        CONST {Thy = "transfer", Name, ...} =>
        mem Name ["bitotal", "bi_unique", "equalityp", "left_unique",
                  "right_unique", "surj", "total"]
      | _ => false
fun is_relconstraint t = relconstraint_tm (rator t)

fun sq ~> f = seq.flatten (seq.map f sq)
fun sqreturn x = seq.fromList [x]
fun sq1 +++ sq2 =
    case seq.cases sq1 of
        NONE => sq2
      | _ => sq1
val fail = seq.empty
fun sqfold f [] th = sqreturn th
  | sqfold f (x::xs) th = seq.bind (f x th) (sqfold f xs)

fun seqrptUntil P f x =
    if P x then seq.fromList [x]
    else f x ~> seqrptUntil P f

fun seqrpt f x = seqrptUntil (List.all is_relconstraint o hyp) f x



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

val FUN_REL_t = prim_mk_const{Thy = "quotient", Name = "===>"}
structure ruledb =
struct
type t = {
  left: thm Net.net,
  right : thm Net.net,
  safe : thm Net.net,
  bad : term Net.net,
  atomic_terms : (string * term) Net.net,
  DOMRNG_ss : thm list
}

val empty_rdb : t =
   {left = Net.empty, right = Net.empty, safe = Net.empty, bad = Net.empty,
    DOMRNG_ss = [], atomic_terms = Net.empty}

fun safenet (t:t) = #safe t
fun badnet (t:t) = #bad t
fun domrngs (t:t) = #DOMRNG_ss t
fun atomic_termnet (t:t) = #atomic_terms t

(* fupdates *)
open FunctionalRecordUpdate
fun mkUp z = makeUpdate6 z
fun update_T z = let
  fun from atomic_terms bad DOMRNG_ss left right safe =
    {atomic_terms = atomic_terms, bad = bad, DOMRNG_ss = DOMRNG_ss, left = left,
     right = right, safe = safe}
  (* fields in reverse order to above *)
  fun from' safe right left DOMRNG_ss bad atomic_terms =
    {atomic_terms = atomic_terms, bad = bad, DOMRNG_ss = DOMRNG_ss, left = left,
     right = right, safe = safe}
  (* first order *)
  fun to f {atomic_terms, bad, DOMRNG_ss, left, right, safe} =
      f atomic_terms bad DOMRNG_ss left right safe
in
  mkUp (from, from', to)
end z

fun fupd_atomic_terms f (t:t) : t =
    update_T t (U #atomic_terms (f (#atomic_terms t))) $$
fun fupd_DOMRNG_ss f (t:t) : t = update_T t (U #DOMRNG_ss (f (#DOMRNG_ss t))) $$
fun fupd_bad f (t:t) : t = update_T t (U #bad (f (#bad t))) $$
fun fupd_left f (t:t) : t = update_T t (U #left (f (#left t))) $$
fun fupd_right f (t:t) : t = update_T t (U #right (f (#right t))) $$
fun fupd_safe f (t:t) : t = update_T t (U #safe (f (#safe t))) $$

fun addrule0 (th, r) =
    let
      val th = UNDISCH_ALL th handle HOL_ERR _ => th
    in
      r |> fupd_left (Net.insert (lhand (concl th), th))
        |> fupd_right(Net.insert (rand (concl th), th))
    end

fun addrule th r = List.foldl addrule0 r (CONJUNCTS th)

fun addsafe th r = r |> fupd_safe (Net.insert (concl th, th))
fun addbad t r = r |> fupd_bad (Net.insert(t,t))
fun add_domrng th r = r |> fupd_DOMRNG_ss (cons th)

fun lookup_rule cleftp (rdb:t) t =
    let
      val n = if cleftp then #left rdb else #right rdb
      val t = if cleftp then lhand t else rand t
    in
      Net.match t n
    end

fun check_for_atom (rdb:t) ct =
    let val pats = Net.match ct (atomic_termnet rdb)
    in
      List.exists (fn (_, p) => can (match_term p) ct) pats
    end

end (* ruledb struct *)


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
    let val pv = pmk_var(#1 (dest_var bv) (* ^ Int.toString i *), i)
        val vmap' = Binarymap.insert(vmap, bv, pv)
        val ((vmap'',i'), result) = m (vmap', i + 1)
    in
      ((vmap, i'), (pv, result))
    end
in
val env0:env = (Binarymap.mkDict Term.compare, 0)
fun build_preterm rdb ct : Preterm.preterm t =
    let
      fun varmap ct e =
          case Binarymap.peek(e,ct) of
              NONE => raise Fail ("Free variable: "^term_to_string ct)
            | SOME pt => return pt
      fun recurse ct =
          if ruledb.check_for_atom rdb ct then
            newconst
          else
            case dest_term ct of
                VAR _ => getmap >>- varmap ct
              | CONST _ => newconst
              | COMB(t1,t2) => lift pmk_comb
                                    (recurse t1 >* recurse t2)
              | LAMB(bv,body) => lift pmk_abs (newvar bv (recurse body))
    in
      recurse ct
    end
end (* local *)

fun dvty ty = ty |> dest_vartype |> (fn s => String.extract(s,1,NONE))
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

fun build_skeleton rdb ct =
    let val ((_, i), pt) = build_preterm rdb ct env0
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



val GFUN_REL_COMB = GEN_ALL FUN_REL_COMB
val GFUN_REL_COMB_EQ = GEN_ALL FUN_REL_COMB_EQ
fun first f [] = NONE
  | first f (x::xs) = SOME (f x) handle HOL_ERR _ => first f xs


fun prove_relation_thm rdb cleftp ct skt =
    let
      fun recurse ct skt =
          let
            val argl = if cleftp then [ct, skt] else [skt, ct]
            val skty = type_of skt and cty = type_of ct
          in
            if ruledb.check_for_atom rdb ct then
              ASSUME (list_mk_comb(ty2relvar cleftp skty cty, argl))
            else
              case dest_term ct of
                  VAR _ =>
                    ASSUME (list_mk_comb(ty2relvar cleftp skty cty, argl))
                | CONST _ =>
                    ASSUME (list_mk_comb(ty2relvar cleftp skty cty, argl))
                | COMB(cf, cx) =>
                  let
                    val fthm = recurse cf (rator skt)
                    val xthm = recurse cx (rand skt)
                    val cj = CONJ fthm xthm
                  in
                    MATCH_MP GFUN_REL_COMB cj
                    handle HOL_ERR _ =>
                           UNDISCH (MATCH_MP GFUN_REL_COMB_EQ cj)
                  end
                | LAMB (cbv, cbod) =>
                  let
                    val (skbv, skbod) = dest_abs skt
                    val brel = ty2relvar cleftp (type_of skbv) (type_of cbv)
                    val b_asm_t =
                        list_mk_comb(brel,
                                     if cleftp then [cbv, skbv]
                                     else [skbv, cbv])
                    val bod_thm = recurse cbod skbod
                    val (lv,rv) = if cleftp then (cbv,skbv) else (skbv,cbv)
                    val hyp_thm =
                        bod_thm
                          |> CONV_RULE
                               (FORK_CONV (UNBETA_CONV lv, UNBETA_CONV rv))
                          |> DISCH b_asm_t |> GENL [lv,rv]
                  in
                    EQ_MP (PART_MATCH lhs (GSYM FUN_REL_def) (concl hyp_thm))
                          hyp_thm
                    end
          end
    in
      recurse ct skt
    end


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


local
  fun nosimpfails h th = if null (free_vars h) then fail else sqreturn th
in
fun simphyp ruledb h th =
    if not (is_relconstraint h) then sqreturn th
    else
      let
        val hth = SIMP_CONV transfer_ss (ruledb.domrngs ruledb) h
      in
        if rhs (concl hth) ~~ T then
          sqreturn $ PROVE_HYP (EQT_ELIM hth) th
        else if null (free_vars h) then fail
        else
          sqreturn $ PROVE_HYP (EQ_IMP_RULE hth |> #2 |> UNDISCH) th
      end handle UNCHANGED => nosimpfails h th
               | HOL_ERR _ => nosimpfails h th
fun simphyps rdb th = sqfold (simphyp rdb) (hyp th) th
end

fun check {cleftp,forceprogress} (ruledb:ruledb.t) th =
    let
      val argsel = if cleftp then lhand else rand
      val ctys = type_vars_in_term (th |> concl |> argsel)
      val hs = hyp th
      fun u1 h th rule =
          case eliminate_with_unifier ctys rule h th of
              NONE => fail
            | SOME th' =>
              let open HOLset
              in
                sqreturn (true, th',
                          listItems $ difference(hypset th', hypset th))
              end
      fun safe_recurse hs (progressed,th) =
          case hs of
              [] => sqreturn (progressed,th)
            | h::rest =>
              let
                val ths = Net.match h (ruledb.safenet ruledb)
              in
                ((seq.fromList ths ~> u1 h th) +++
                 sqreturn(progressed, th,[])) ~>
                (fn (p,th',newhs) => safe_recurse (newhs @ rest) (p,th'))
              end
      fun bad_recurse hs th =
          case hs of
              [] => sqreturn th
            | h::rest =>
                if List.exists
                     (fn pat => can (match_term (gen_tyvarify pat)) h)
                     (Net.match h (ruledb.badnet ruledb))
                then
                  fail
                else bad_recurse rest th
      fun assertprogress (p, th) = if not p andalso forceprogress then fail
                                   else sqreturn th
    in
      safe_recurse hs (false,th) ~> assertprogress ~> simphyps ruledb ~>
      S (C bad_recurse) hyp
    end

fun check_constraints cleftp rdb th =
    check{cleftp=cleftp,forceprogress=false} rdb th

val core_theories = ["bool", "min", "list", "pred_set", "bag",
                     "combin", "pair", "sum", "one"]

fun thy_in_type thy ty =
    let
      fun recurse tys =
          case tys of
              [] => false
            | [] :: rest => recurse rest
            | (ty::rest1) :: rest2 =>
              if is_vartype ty then recurse (rest1::rest2)
              else let val {Thy,Tyop,Args} = dest_thy_type ty
                   in
                     Thy = thy orelse
                     recurse (Args::rest1::rest2)
                   end
    in
      recurse [[ty]]
    end

fun chainPreds Ps set =
    case Ps of
        [] => HOLset.find (K true) set
      | P::rest => (case HOLset.find P set of
                        SOME a => SOME a
                      | NONE => chainPreds rest set)

fun resolve_relhyps hints cleftp rdb th =
    let
      val (argsel,oppsel) = if cleftp then (lhand,rand) else (rand,lhand)
      val ctys = type_vars_in_term (th |> concl |> argsel)
      val fail = seq.empty
      fun goodname nm t = #Name (dest_thy_const (argsel t)) = nm
                          handle HOL_ERR _ => false
      fun goodthy0 thys t =
          let val {Thy,...} = dest_thy_const (argsel t)
          in
            not (mem Thy thys)
          end handle HOL_ERR _ => false
      val goodthy = goodthy0 core_theories
      val notboolthy = goodthy0 ["min", "bool"]
      fun current_typed t =
          thy_in_type (current_theory()) (type_of (oppsel t))
      fun goodhyp h = not (is_relconstraint h)
      val goods0 = HOLset.filter goodhyp (hypset th)
    in
      if HOLset.isEmpty goods0 then fail
      else
        case chainPreds
               (map goodname hints @ [goodthy, notboolthy, current_typed])
               goods0
         of
            NONE => fail
          | SOME h =>
            let
              val last_resorts = [UNDISCH equalityp_applied]
              val candidate_rules =
                  ruledb.lookup_rule cleftp rdb h @ last_resorts

              fun kont candidate_rule =
                  case eliminate_with_unifier ctys candidate_rule h th of
                      NONE => fail
                    | SOME th' => sqreturn th'
              val iff_strengtheners =
                  let
                    val (Rx, y) = dest_comb h
                    val (R, x) = dest_comb Rx
                  in
                    if rand R ~~ implication then
                      kont $ UNDISCH FUN_REL_iff_imp_strengthen
                    else if rand R ~~ cimp_tm then
                      kont $ UNDISCH FUN_REL_iff_cimp_strengthen
                    else fail
                  end handle HOL_ERR _ => fail
            in
              ((seq.fromList candidate_rules ~> kont) +++ iff_strengtheners) ~>
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



val ruledb =
    let
      open ruledb
      fun munge th = UNDISCH_ALL (REWRITE_RULE [GSYM AND_IMP_INTRO] th)
    in
      empty_rdb
        |> addrule EQ_bi_unique
        |> addrule UPAIR_COMMA
        |> addrule ALL_total_cimp_cimp
        |> addrule ALL_total_iff_cimp
        |> addrule ALL_surj_imp_imp
        |> addrule ALL_IFF
        |> addrule ALL_surj_RDOM
        |> addrule ALL_total_RRANGE
        |> addrule ALL_total_iff_imp_RRANGE
        |> addrule ALL_surj_iff_imp (* best for quotient type situations *)
        |> addrule EXISTS_total_iff_imp
        |> addrule EXISTS_total_imp_imp
        |> addrule EXISTS_surj_iff_cimp
        |> addrule EXISTS_surj_cimp_cimp
        |> addrule EXISTS_IFF_RDOM
        |> addrule EXISTS_IFF_RRANGE
        |> addrule EXISTS_bitotal
        |> addrule COND_rule
        |> addrule UREL_EQ
        |> addrule PAIRU_COMMA
        |> addrule pair_CASE_CONG
        |> addrule LET_rule
        |> addrule FUNPOW_rule
        |> addrule FST_CORRECT
        |> addrule SND_CORRECT
        |> addrule COMMA_CORRECT
        |> addrule option_CASE_CONG
        |> addrule SOME_rule
        |> addrule NONE_rule
        |> addrule OPTION_BIND_rule
        |> addrule list_CASE_CONG
        |> addrule NIL_rule
        |> addrule CONS_rule
        |> addrule TL_rule
        |> addrule LENGTH_rule
        |> addrule FOLDL_rule
        |> addrule FOLDR_rule
        |> addrule MAP_rule
        |> addrule ALL_DISTINCT_rule
        |> addrule cimp_imp
        |> addrule (equalityp_applied
                      |> INST_TYPE [alpha |-> (bool --> bool --> bool)]
                      |> INST [mk_var("x", bool --> bool --> bool) |->
                               boolSyntax.implication])
        |> addsafe (munge equalityp_FUN_REL)
        |> addsafe (munge equalityp_PAIR_REL)
        |> addsafe (munge equalityp_OPTREL)
        |> addsafe (munge equalityp_LIST_REL)
        |> addsafe (munge bi_unique_implied)
        |> addsafe (munge bitotal_implied)
        |> addsafe (munge total_total_sets)
        |> addsafe (munge surj_sets)
        |> addsafe eq_equalityp
        |> addsafe bi_unique_EQ
        |> addsafe bitotal_EQ
        |> addsafe total_EQ
        |> addsafe left_unique_EQ
        |> addsafe right_unique_EQ
        |> addsafe surj_EQ
        |> addsafe (SPEC_ALL EQ_REFL)
        |> addsafe (UNDISCH_ALL LIST_REL_surj)
        |> addsafe (UNDISCH_ALL LIST_REL_total)
        |> addsafe (UNDISCH_ALL LIST_REL_left_unique)
        |> addsafe (UNDISCH_ALL LIST_REL_right_unique)
        |> addsafe (UNDISCH_ALL OPTREL_left_unique)
        |> addsafe (UNDISCH_ALL OPTREL_right_unique)
        |> addsafe (UNDISCH_ALL OPTREL_total)
        |> addsafe (UNDISCH_ALL OPTREL_surj)
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
        |> add_domrng quotientTheory.FUN_REL_EQ
        |> add_domrng surj_EQ
        |> fupd_atomic_terms
             (Net.insert(numeral_pattern,("numeral", numeral_pattern)))
    end (* let *)

fun search_for P sq =
    let
      fun recurse sq =
          case seq.cases sq of
              NONE => raise Fail "No theorems!"
            | SOME (th, rest) => if P (concl th) then th
                                 else recurse rest
    in
      recurse sq
    end

fun const_occurs c = can (find_term (same_const c))
val RRANGE_tm = prim_mk_const{Thy = "relation", Name = "RRANGE"}
val RDOM_tm = prim_mk_const{Thy = "relation", Name = "RDOM"}
val iff_tm = mk_thy_const{Thy = "min", Name = "=", Ty = bool --> bool --> bool}
fun transfer_skeleton rdb (c:config) t =
    let
      val th0 = prove_relation_thm rdb (#cleftp c) t (build_skeleton rdb t)
      val tgt = if #force_imp c then boolSyntax.implication
                else iff_tm
      val (topf, _) = strip_comb (concl th0)
      val (tmsubst, tysubst) = match_term topf tgt
    in
          INST tmsubst (INST_TYPE tysubst th0)
    end

fun resolveN n hints cleftp ruledb t =
    let
      fun recurse n th =
          if n < 1 then sqreturn th
          else resolve_relhyps hints cleftp ruledb th ~> recurse (n - 1)
    in
      recurse n
        (transfer_skeleton ruledb {cleftp=cleftp,force_imp=false,hints=hints} t)
    end

fun transfer_phase1 (cfg:config as {cleftp,hints,...}) ruledb t =
    let
      open simpLib boolSimps
    in
      seqrpt (resolve_relhyps hints cleftp ruledb)
             (transfer_skeleton ruledb cfg t) ~>
      seqrpt (check{cleftp=cleftp,forceprogress=true} ruledb)
    end

fun eliminate_domrng cleftp (ruledb:ruledb.t) =
    let
      val argsel = if cleftp then RAND_CONV else LAND_CONV
    in
      CONV_RULE (argsel $ SIMP_CONV transfer_ss (ruledb.domrngs ruledb))
    end

fun base_transfer (cfg:config) ruledb t =
    let
      open simpLib boolSimps
      val {cleftp,...} = cfg
      val argsel = if cleftp then RAND_CONV else LAND_CONV
    in
      transfer_phase1 cfg ruledb t |>
      seq.map (mkrelsyms_eq cleftp) ~>
      simphyps ruledb ~>
      check {cleftp=cleftp,forceprogress=false} ruledb |>
      seq.map (eliminate_domrng cleftp ruledb) |>
      seq.filter (not o const_occurs RRANGE_tm o concl) |>
      seq.filter (not o const_occurs RDOM_tm o concl)
    end

fun nontrivial t = lhand t !~ rand t
fun transfer_tm depth cfg ruledb t =
    base_transfer cfg ruledb t |> search_for nontrivial

fun transfer_thm depth (cfg:config) ruledb th =
    let
      fun goodconcl c = lhand c !~ rand c handle HOL_ERR _ => false
      val th0 = base_transfer cfg ruledb (concl th) |> search_for goodconcl
    in
      if is_eq (concl th0) then
        if #cleftp cfg then EQ_MP th0 th else EQ_MP (SYM th0) th
      else MP th0 th
    end

fun is_flipimp t =
    let val (impp, _, _) = combinSyntax.dest_C t
    in
      same_const impp boolSyntax.implication
    end handle HOL_ERR _ => false

val default_depth = Sref.new 4
val the_ruledb = Sref.new ruledb
fun xfer_tac cleftp hints (g as (asl,c)) =
    let
      val th = transfer_tm (Sref.value default_depth)
                           {hints = hints, cleftp = cleftp, force_imp = false}
                           (Sref.value the_ruledb) c
      val (is_imp', impc, impa, imp_munge, eql, eqr, eqmunge) =
          if cleftp then
            (is_flipimp, lhand, rand, CONV_RULE (REWR_CONV combinTheory.C_THM),
             lhand, rand, I)
          else (is_imp, rand, lhand, I, rand, lhand, SYM)
      val con = concl th
      val mkE = mk_HOL_ERR "transferLib" "xfer_tac"
    in
      if aconv con c then ACCEPT_TAC th g
      else if is_imp' con then
        if aconv (impc con) c then
          if aconv (impa con) c then
            raise mkE "Derived p ==> p implication"
          else Tactic.MATCH_MP_TAC (imp_munge th) g
        else raise mkE "Derived an implication, but conclusion <> goal"
      else if is_eq con andalso aconv (eql con) c then
        if aconv (eqr con) c then raise mkE "Derived p <=> p equality"
        else CONV_TAC (REWR_CONV (eqmunge th)) g
      else raise mkE ("Derived non-equality, non-implication: "^
                      term_to_string con)
    end

fun SPEC_ALL_TAC (asl,g) =
    (rpt (pop_assum mp_tac) >>
     map_every (fn v => SPEC_TAC (v,v))
               (HOLset.listItems $ FVL (g::asl) empty_tmset))
    (asl,g)
fun xfer_back_tac hs = SPEC_ALL_TAC >> xfer_tac false hs
fun xfer_fwd_tac hs = SPEC_ALL_TAC >> xfer_tac true hs

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


(* setting up atomic terms store *)
datatype ATM_DELTA = ADD of string * term | DEL of string
fun ATM_apply_delta (ADD nmt) l = nmt :: l
  | ATM_apply_delta (DEL s) l = List.filter (fn (s',_) => s' <> s) l
val atms_adinfo = {tag = "transfer_atomic_term",
                   initial_values = [("min", [])],
                   apply_delta = ATM_apply_delta}
local open ThyDataSexp infix ||
in
val dec_delta : ATM_DELTA dec =
  Option.map ADD o pair_decode (string_decode, term_decode) ||
  Option.map DEL o string_decode
fun enc_delta (ADD (s,t)) = pair_encode(String, Term) (s,t)
  | enc_delta (DEL s) = String s
end

fun uptodate_delta (ADD(_,t)) = Term.uptodate_term t
  | uptodate_delta _ = true

fun apply_to_ruledb (ADD (nmt as (n,t))) rdb =
    fupd_atomic_terms (Net.insert(t,nmt)) rdb
  | apply_to_ruledb (DEL nm) rdb =
    fupd_atomic_terms (Net.filter (fn (n,t) => n <> nm)) rdb

val adresult = AncestryData.fullmake {
      adinfo = atms_adinfo,
      uptodate_delta = uptodate_delta,
      sexps = {dec = dec_delta, enc = enc_delta},
      globinfo = {initial_value = [],
                  thy_finaliser = NONE,
                  apply_to_global =
                  fn d => fn l => (ATM_apply_delta d l before
                                   Sref.update the_ruledb (apply_to_ruledb d))}
    }

fun temp_add_atomic_term nmt =
    Sref.update the_ruledb (apply_to_ruledb (ADD nmt))
fun add_atomic_term nmt =
      (#record_delta adresult (ADD nmt);
       temp_add_atomic_term nmt)
val atomic_terms = #get_global_value adresult

fun global_ruledb() = Sref.value the_ruledb


end (* struct *)
