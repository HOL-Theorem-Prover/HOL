structure bnfLib :> bnfLib =
struct

open HolKernel boolLib bnfBase stmonad
open bnfPrelimsTheory

type info = thm bnfBase_dtype.info

val ERR = mk_HOL_ERR "bnfLib"

(* ----------------------------------------------------------------------
    turning a datatype specification into the type of the functor whose
    fixed point it is
   ---------------------------------------------------------------------- *)

type convert_state = {
  tyvars : hol_type Symtab.table * int,
  mutrecvars : hol_type Symtab.table * int
}
fun updtyvars f {tyvars,mutrecvars} =
    {tyvars = f tyvars, mutrecvars = mutrecvars}
fun updmvs f {tyvars,mutrecvars} =
    {tyvars = tyvars, mutrecvars = f mutrecvars}
fun updtab p (tab,c) = (Symtab.update p tab, c + 1)

fun cs_tylookup s (cst:convert_state) =
    (cst, Symtab.lookup (#1 (#tyvars cst)) s)
fun cs_mvlookup s (cst:convert_state) =
    (cst, Symtab.lookup (#1 (#mutrecvars cst)) s)

fun newty k (cst:convert_state) =
    let val new = mk_vartype ("'b" ^ Int.toString (#2 (#tyvars cst)))
    in
      (updtyvars (updtab (k,new)) cst, new)
    end
fun newmv k (cst:convert_state) =
    let val new = mk_vartype("'a" ^ Int.toString (#2 (#mutrecvars cst)))
    in
      (updmvs (updtab (k, new)) cst, new)
    end

val empty_cstate = {tyvars = (Symtab.empty, 1), mutrecvars = (Symtab.empty, 1)}

fun convertTy ty =
    if is_vartype ty then
      let val oldnm = dest_vartype ty
      in
        cs_tylookup oldnm >-
        (fn opt =>
          case opt of
             NONE => newty oldnm
           | SOME ty' => return ty')
      end
    else
      let val {Thy,Tyop,Args} = dest_thy_type ty
      in
        mmap convertTy Args >-
        (fn args' =>
          return (mk_thy_type{Args = args',Tyop=Tyop,Thy=Thy}))
      end

(* assume that ftor is used only when at least one of the arguments does
   contain an instance of the_arg or a mutrec_var *)
fun specToFunctor0 s =
    case s of
        ftor (knm, args) =>
        mmap specToFunctor0 args >-
        (fn args' =>
            return $ mk_thy_type{
              Args = args', Thy = #Thy knm, Tyop = #Name knm})
      | the_arg => return alpha
      | constty ty => convertTy ty
      | mutrec_var s =>
        cs_mvlookup s >-
        (fn opt =>
            case opt of
                NONE => newmv s
              | SOME ty => return ty)
      | previous_op s => raise Fail "previous_op encountered in specToFunctor0"

fun specToFunctor s = #2 (specToFunctor0 s empty_cstate)

(* ----------------------------------------------------------------------
    recognising a stored BNF's map constant.  The type of

       map : (α₁ → γ₁) → ... → (αₙ → γₙ) → (α₁,...,αₙ,β₁,...)F →
             (γ₁,...,γₙ,β₁,...)F

    identifies the "live" arguments as those named 'aᵢ (with the
    corresponding function argument going to 'cᵢ).
   ---------------------------------------------------------------------- *)

fun is_maparg ty =
    let val (d,r) = dom_rng ty
        val dnm = dest_vartype d
        val rnm = dest_vartype r
        val dsfx = String.extract(dnm, 2, NONE)
        val rsfx = String.extract(rnm, 2, NONE)
    in
      String.isPrefix "'a" dnm andalso String.isPrefix "'c" rnm andalso
      dsfx = rsfx andalso CharVector.all Char.isDigit dsfx
    end handle Subscript => false | HOL_ERR _ => false

fun strip_mapargs ty =
    let val (d,r) = dom_rng ty
    in
      if is_maparg d then
        let val (rest, base) = strip_mapargs r
        in
          (d::rest, base)
        end
      else ([], (d,r))
    end

fun is_alphanum_tyv ty =
    let val s = dest_vartype ty
    in
      String.isPrefix "'a" s andalso size s > 2 andalso
      CharVector.all Char.isDigit (String.extract(s, 2, NONE))
    end

(* ----------------------------------------------------------------------
    term-building utilities for the pieces a composite's map and set
    functions are made of
   ---------------------------------------------------------------------- *)

val map_f = mk_var("f", alpha --> beta)
val equal_alpha = boolSyntax.equality
val empty_alpha = pred_setSyntax.mk_empty alpha
fun K0 ty =
    mk_comb(
      Term.inst[alpha |-> (alpha --> bool), beta |-> ty] combinSyntax.K_tm,
      empty_alpha
    )
fun Ityped ty = Term.inst [alpha |-> ty] combinSyntax.I_tm

val aset_ty = alpha --> bool
val bset_ty = beta --> bool
val BIMG = let (* (o) BIGUNION o IMAGE ; generating an α set; other var is β *)
  val imgtm = mk_thy_const{
        Thy = "pred_set", Name = "IMAGE",
        Ty = (beta --> aset_ty) --> bset_ty --> (aset_ty --> bool)}
  val bu_tm = pred_setSyntax.bigunion_tm
  val o1_tm = mk_thy_const{
        Thy = "combin", Name = "o",
        Ty = type_of bu_tm --> (bset_ty --> (aset_ty --> bool)) -->
             (bset_ty --> aset_ty)}
  val obu = mk_comb(o1_tm, bu_tm)
in
  combinSyntax.mk_o(obu, imgtm)
end

val UNION_tm = mk_thy_const{
      Thy = "pred_set", Name = "UNION",
      Ty = aset_ty --> (aset_ty --> aset_ty)}

fun mk_lifted_union (f1,f2) =
    (* f1 and f2 have same type, schematically some-β → α set;
       i.e., range type is literally α, domain can vary
       generate S((UNION) o f1)f2
     *)
    let
      val (b,_) = dom_rng (type_of f1)
      val Uof1 = combinSyntax.mk_o(UNION_tm, f1)
      val Stm = mk_thy_const{Thy = "combin", Name = "S",
                             Ty = (b --> (aset_ty --> aset_ty)) -->
                                  ((b --> aset_ty) --> (b --> aset_ty))}
    in
      list_mk_comb(Stm, [Uof1, f2])
    end

(* BIMG f o set *)
fun mk_BIMGo (f, set) =
    let val (fd, _) = dom_rng (type_of f)
    in
      combinSyntax.mk_o(mk_comb(inst [beta |-> fd] BIMG, f), set)
    end

fun mk_IMAGE f =
    let val (d,r) = dom_rng (type_of f)
    in
      mk_comb(mk_thy_const{Thy = "pred_set", Name = "IMAGE",
                           Ty = (d --> r) -->
                                ((d --> bool) --> (r --> bool))},
              f)
    end

val cardleq_tm = prim_mk_const{Thy = "cardinal", Name = "cardleq"}
fun mk_cardleq (l,r) = list_mk_icomb (cardleq_tm, [l,r])
fun dest_cardleq t =
    let val (f,r) = dest_comb t
        val (c,l) = dest_comb f
    in
      if same_const c cardleq_tm then (l,r)
      else raise ERR "dest_cardleq" "not a cardleq application"
    end

(* Instantiating a stored theorem to the case in hand is a forward step:
   nothing here should go through the parser or a tactic. *)
fun inst_thm th target = PART_MATCH I th target
fun inst_forall th target =
    let val (v, body) = dest_forall target
    in
      GEN v (PART_MATCH I th body)
    end

fun biCompare (bI info1, bI info2) =
    Type.compare(#canontype info1, #canontype info2)
val empty_biset : info HOLset.set = HOLset.empty biCompare

(* ----------------------------------------------------------------------
    A "plan" records how a composite functor is built out of the BNFs in
    the database.  Everything that has to be generated for the composite
    (map term, set term, and the theorems about them) is then a separate
    traversal of the plan; each traversal handles one node at a time, so
    the work is linear in the size of the type expression.
   ---------------------------------------------------------------------- *)

datatype fplan =
    FPvar                   (* the functor's own argument, α *)
  | FPconst of hol_type     (* an α-free type; the constant functor *)
  | FPnode of {ty : hol_type, info : info, kids : fkid list}
withtype fkid = {set : term,    (* the node's set fn for this argument *)
                 bnd : term,    (* ... and its bound *)
                 bndthm : thm,  (* |- !x. set x <<= bnd *)
                 sub : fplan}   (* the plan for the argument itself *)

(* instantiate the types of |- !x. set x <<= bnd so that set : setty *)
fun inst_bndthm th setty =
    let val (l,_) = dest_cardleq (concl (SPEC_ALL th))
    in
      INST_TYPE (match_type (type_of (rator l)) setty) th
    end

fun mkplan db ty =
    if ty = alpha then FPvar
    else if not (mem alpha (type_vars ty)) then FPconst ty
    else
      let val {Tyop,Thy,Args} = dest_thy_type ty
      in
        case pure_lookup db {Name = Tyop, Thy = Thy} of
            NONE => raise ERR "mkplan" (Thy ^ "$" ^ Tyop ^ " is not a BNF")
          | SOME (info as bI i) =>
            let
              val (_, (d,_)) = strip_mapargs (type_of (#map i))
              val params = #Args (dest_thy_type d)
              fun sift (_, [], []) = []
                | sift (n, a::As, p::Ps) =
                  if is_alphanum_tyv p then a :: sift(n + 1, As, Ps)
                  else if mem alpha (type_vars a) then
                    raise ERR "mkplan"
                          (Thy ^ "$" ^ Tyop ^
                           " is not functorial in argument " ^ Int.toString n)
                  else sift(n + 1, As, Ps)
                | sift _ = raise ERR "mkplan" "map constant has wrong arity"
              val actuals = sift(0, Args, params)
              fun mkkid (actual, (settm, bth0)) =
                  let
                    val target = ty --> (actual --> bool)
                    val settm' = inst (match_type (type_of settm) target) settm
                    val bth = inst_bndthm bth0 target
                    val (_, bnd) = dest_cardleq (concl (SPEC_ALL bth))
                    val sub = if mem alpha (type_vars actual) then
                                mkplan db actual
                              else FPconst actual
                  in
                    {set = settm', bnd = bnd, bndthm = bth, sub = sub} : fkid
                  end
            in
              FPnode {ty = ty, info = info,
                      kids = ListPair.mapEq mkkid
                               (actuals, ListPair.zipEq(#set i, #bndthms i))}
            end
      end

(* Apply a stored map constant to the maps for its arguments.  The
   instantiation can't be left to list_mk_icomb: a functor's *dead*
   arguments don't appear in the types of its live arguments' maps, so
   they have to be pinned down by matching the map's domain against the
   type the composite uses at this node (srcty is that type with the
   functor's argument replaced by f's own domain). *)
fun apply_map map_t submaps srcty =
    let val (margs, (d,_)) = strip_mapargs (type_of map_t)
        val pat = List.foldr (op -->) d margs
        val tgt = List.foldr (op -->) srcty (List.map type_of submaps)
    in
      list_mk_comb(Term.inst (match_type pat tgt) map_t, submaps)
    end

fun planMap plan f =
    case plan of
        FPvar => f
      | FPconst ty => Ityped ty
      | FPnode {info = bI i, kids, ty, ...} =>
        let
          val submaps = List.map (fn {sub,...} => planMap sub f) kids
          val srcty = type_subst [alpha |-> #1 (dom_rng (type_of f))] ty
        in
          apply_map (#map i) submaps srcty
        end

fun planSet plan =
    case plan of
        FPvar => equal_alpha
      | FPconst ty => K0 ty
      | FPnode {kids, ...} =>
        let
          val lifted =
              List.map (fn {set,sub,...} => mk_BIMGo (planSet sub, set)) kids
        in
          List.foldl (fn (t,A) => mk_lifted_union(A,t)) (hd lifted) (tl lifted)
        end

fun planInfos plan =
    case plan of
        FPvar => []
      | FPconst _ => []
      | FPnode {info, kids, ...} =>
        info :: List.concat (List.map (planInfos o #sub) kids)

fun functorToMapAndSet db ty =
    let val plan = mkplan db ty
    in
      (planMap plan map_f, planSet plan,
       HOLset.addList(empty_biset, planInfos plan))
    end

(* ----------------------------------------------------------------------
    the bound.

    Every component functor comes with its own bound, always of the form
    S ⊆ univ(:τ) for some τ.  Because an infinite cardinal absorbs both
    products and unions, one infinite cardinal dominating all of the
    components' bounds bounds the composite as well; univ(:num + τ₁ + ...
    + τₙ) is such a cardinal.
   ---------------------------------------------------------------------- *)

val num_ty = mk_thy_type{Thy = "num", Tyop = "num", Args = []}
fun mk_sumty (t1,t2) = mk_thy_type{Thy = "sum", Tyop = "sum", Args = [t1,t2]}
fun list_mk_sumty [t] = t
  | list_mk_sumty (t::ts) = mk_sumty(t, list_mk_sumty ts)
  | list_mk_sumty [] = raise ERR "list_mk_sumty" "empty list of types"

fun planBndTypes plan =
    case plan of
        FPvar => []
      | FPconst _ => []
      | FPnode {kids, ...} =>
        List.concat (List.map
                       (fn {bnd,sub,...} =>
                           #1 (dom_rng (type_of bnd)) :: planBndTypes sub)
                       kids)

(* |- univ(:ty) <<= univ(:list_mk_sumty tys), where ty occurs in tys *)
fun univ_le tys ty =
    case tys of
        [] => raise ERR "univ_le" "bound type not among the component bounds"
      | [t] => if t = ty then
                 ISPEC (pred_setSyntax.mk_univ ty) cardinalTheory.cardleq_REFL
               else raise ERR "univ_le"
                          "bound type not among the component bounds"
      | t::rest =>
        let val restty = list_mk_sumty rest
        in
          if t = ty then
            INST_TYPE [alpha |-> t, beta |-> restty] UNIV_CARD_LE_ADDR
          else
            MATCH_MP cardinalTheory.cardleq_TRANS
                     (CONJ (univ_le rest ty)
                           (INST_TYPE [alpha |-> t, beta |-> restty]
                                      UNIV_CARD_LE_ADDL))
        end

fun planBndThm (B, Bne, Binf, bndtys) plan =
    let val st = planSet plan
        val x = mk_var("x", #1 (dom_rng (type_of st)))
        val goal = mk_forall(x, mk_cardleq(mk_comb(st,x), B))
    in
      case plan of
          FPvar => inst_forall (MATCH_MP EQ_CARDLE Bne) goal
        | FPconst _ => inst_forall K0_CARDLE goal
        | FPnode {kids, ...} =>
          let
            fun kidthm ({set,bnd,bndthm,sub}:fkid) =
                let
                  val subth = planBndThm (B,Bne,Binf,bndtys) sub
                  val bnd_le_B =
                      MATCH_MP cardinalTheory.cardleq_TRANS
                               (CONJ (ISPEC bnd cardinalTheory.CARD_LE_UNIV)
                                     (univ_le bndtys
                                              (#1 (dom_rng (type_of bnd)))))
                  val y = mk_var("y", #1 (dom_rng (type_of set)))
                  val setth = GEN y (MATCH_MP cardinalTheory.cardleq_TRANS
                                              (CONJ (SPEC y bndthm) bnd_le_B))
                in
                  MATCH_MP BIMGo_CARDLE (LIST_CONJ [Binf, subth, setth])
                end
            val lifted = List.map kidthm kids
            fun combine (t,A) = MATCH_MP LU_CARDLE (LIST_CONJ [Binf, A, t])
            val res = List.foldl combine (hd lifted) (tl lifted)
          in
            if aconv (concl res) goal then res
            else raise ERR "planBndThm"
                       ("derived " ^ thm_to_string res ^ "; wanted " ^
                        term_to_string goal)
          end
    end

fun planBnd plan =
    let
      val tys = num_ty :: List.filter (not o equal num_ty)
                                      (op_mk_set equal (planBndTypes plan))
      val B = pred_setSyntax.mk_univ (list_mk_sumty tys)
      val Binf = case tl tys of
                     [] => pred_setTheory.num_INFINITE
                   | rest => INST_TYPE [alpha |-> list_mk_sumty rest]
                                       INFINITE_num_sum
      val Bne = MATCH_MP INFINITE_NOT_EMPTY Binf
    in
      (B, Binf, planBndThm (B, Bne, Binf, tys) plan)
    end

(* ----------------------------------------------------------------------
    the map laws
   ---------------------------------------------------------------------- *)

(* rewrite |- !f.. x. setᵢ (map f.. x) = IMAGE fᵢ (setᵢ x) into the
   point-free |- setᵢ o map f.. = IMAGE fᵢ o setᵢ *)
val mapIMG_ofy =
    SPEC_ALL o
    CONV_RULE (
      STRIP_QUANT_CONV
        (BINOP_CONV (PURE_ONCE_REWRITE_CONV [GSYM combinTheory.o_THM])) THENC
      BINDER_CONV (PURE_REWRITE_CONV [GSYM FUN_EQ_THM]))

(* instantiate the equational theorem th so that its LHS is target *)
fun inst_lhs th target =
    let val th' = SPEC_ALL th
        val (tmS, tyS) = match_term (lhs (concl th')) target
    in
      INST tmS (INST_TYPE tyS th')
    end

fun planMapID plan =
    case plan of
        FPvar => REFL (Ityped alpha)
      | FPconst ty => REFL (Ityped ty)
      | FPnode {info = bI i, kids, ...} =>
        let
          val kidths = List.map (planMapID o #sub) kids
          val hdtm = #1 (strip_comb (planMap plan (Ityped alpha)))
          val cong =
              List.foldl (fn (kth,A) => MK_COMB(A,kth)) (REFL hdtm) kidths
        in
          TRANS cong (inst_lhs (#mapID i) (rhs (concl cong)))
        end

fun planMapO (f,g) plan =
    case plan of
        FPvar => REFL (combinSyntax.mk_o(f,g))
      | FPconst ty => CONJUNCT1 (ISPEC (Ityped ty) combinTheory.I_o_ID)
      | FPnode {info = bI i, kids, ...} =>
        let
          val step1 = inst_lhs (#mapO i)
                        (combinSyntax.mk_o(planMap plan f, planMap plan g))
          val kidths = List.map (planMapO (f,g) o #sub) kids
          val hdtm = #1 (strip_comb (rhs (concl step1)))
          val step2 = List.foldl (fn (kth,A) => MK_COMB(A,kth)) (REFL hdtm)
                                 kidths
        in
          TRANS step1 step2
        end

fun planMapIMAGE (f, instB) plan =
    case plan of
        FPvar => ISPEC f EQ_natural
      | FPconst ty =>
        inst_thm K0_natural
                 (mk_eq(combinSyntax.mk_o(instB (K0 ty), Ityped ty),
                        combinSyntax.mk_o(mk_IMAGE f, K0 ty)))
      | FPnode {info = bI i, kids, ...} =>
        let
          val mp = planMap plan f
          fun kidthm (({set,sub,...}:fkid), imgth) =
              MATCH_MP BIMG_o_natural
                       (CONJ (inst_lhs (mapIMG_ofy imgth)
                                       (combinSyntax.mk_o(instB set, mp)))
                             (planMapIMAGE (f,instB) sub))
          val kths = ListPair.mapEq kidthm (kids, #mapIMAGE i)
        in
          List.foldl (fn (t,A) => MATCH_MP LU_natural (CONJ A t))
                     (hd kths) (tl kths)
        end

(* the hypothesis of the composite's congruence theorem talks about the
   whole of the composite's set; break it up into the parts that the
   node's own congruence theorem needs *)
fun splitLU th n =
    if n <= 1 then [th]
    else
      let val p = MATCH_MP LU_CONG_hyp th
      in splitLU (CONJUNCT1 p) (n - 1) @ [CONJUNCT2 p] end

fun planMapCONG (f,g) plan =
    let
      val setA = planSet plan
      val ty = #1 (dom_rng (type_of setA))
      val x = mk_var("x", ty)
      val a = mk_var("a", alpha)
      val hyp = mk_forall(a,
                  mk_imp(pred_setSyntax.mk_in(a, mk_comb(setA,x)),
                         mk_eq(mk_comb(f,a), mk_comb(g,a))))
    in
      case plan of
          FPvar => ISPECL [f,g,x] EQ_CONG
        | FPconst _ => DISCH hyp (REFL (mk_comb(Ityped ty, x)))
        | FPnode {info = bI i, kids, ...} =>
          let
            val kidhyps = splitLU (ASSUME hyp) (length kids)
            fun kidfact (({set,sub,...}:fkid), khyp) =
                let
                  val sty = #1 (dom_rng (type_of (planSet sub)))
                  val y = mk_var("y", sty)
                  val ymem = pred_setSyntax.mk_in(y, mk_comb(set, x))
                  val subhyp = MATCH_MP BIMG_o_CONG_hyp
                                        (CONJ khyp (ASSUME ymem))
                  val ih = INST [mk_var("x", sty) |-> y]
                                (planMapCONG (f,g) sub)
                in
                  GEN y (DISCH ymem (MP ih subhyp))
                end
            val facts = ListPair.mapEq kidfact (kids, kidhyps)
          in
            DISCH hyp (MATCH_MP (GEN_ALL (#mapCONG i)) (LIST_CONJ facts))
          end
    end

(* ----------------------------------------------------------------------
    nonemptiness.

    Constructing a fixed point for the composite needs two facts beyond
    the BNF laws: that the composite has an element whose set is empty
    (otherwise the algebra over ∅ is itself empty, and the fixed point
    can't be built), and that its set is not *always* empty (otherwise
    the fixed point is trivial).  Both come out of the witnesses each
    component functor was registered with, composed the same way the map
    and set terms are: see Blanchette, Popescu and Traytel, "Witnessing
    (Co)datatypes", ESOP 2015.
   ---------------------------------------------------------------------- *)

fun mk_arb ty = mk_thy_const{Thy = "bool", Name = "ARB", Ty = ty}
fun actual_of ({sub,...}:fkid) = #1 (dom_rng (type_of (planSet sub)))

(* instantiate a witness's term and theorem so that the term takes the
   plan's actual argument types and lands in ty *)
fun inst_wit (wtm, wth) actuals ty =
    let val theta = match_type (type_of wtm) (List.foldr (op -->) ty actuals)
    in
      (Term.inst theta wtm, INST_TYPE theta wth)
    end

(* (w, |- set w = ∅), when the composite has such a w.  It doesn't when
   an element can't be built without supplying the functor's argument, as
   in ‘:'a # 'a option’; there every element's set is inhabited. *)
fun planWitness plan =
    case plan of
        FPvar => NONE
      | FPconst ty =>
        let val w = mk_arb ty
        in
          SOME (w, inst_thm K0_EMPTY (mk_eq(mk_comb(K0 ty, w), empty_alpha)))
        end
      | FPnode {info = bI i, kids, ty} =>
        let
          val actuals = List.map actual_of kids
          fun tryWit wit =
              let
                val (wtm, wth) = inst_wit wit actuals ty
                (* which of the functor's arguments this witness needs *)
                val needs = List.map (not o pred_setSyntax.is_empty o rand)
                                     (strip_conj (concl (SPEC_ALL wth)))
                (* an argument to pass, and a proof that everything the
                   node's set function can produce there has empty set *)
                fun kidarg (needed, kid as {sub,...} : fkid) =
                    if needed then
                      case planWitness sub of
                          NONE => NONE
                        | SOME (t,th) => SOME (t, MATCH_MP SING_ALL th)
                    else
                      SOME (mk_arb (actual_of kid),
                            ISPEC (planSet sub) EMPTY_ALL)
                val kidargs = ListPair.mapEq kidarg (needs, kids)
              in
                if List.exists (not o isSome) kidargs then NONE
                else
                  let
                    val kas = List.map valOf kidargs
                    val args = List.map #1 kas
                    val kths =
                        ListPair.mapEq
                          (fn (c, (_,prem)) =>
                              MATCH_MP BIMGo_EMPTY (CONJ c prem))
                          (CONJUNCTS (SPECL args wth), kas)
                    fun combine (t,A) = MATCH_MP LU_EMPTY (CONJ A t)
                  in
                    SOME (list_mk_comb(wtm, args),
                          List.foldl combine (hd kths) (tl kths))
                  end
              end
          fun firstOK [] = NONE
            | firstOK (w::ws) = (case tryWit w of NONE => firstOK ws | r => r)
        in
          firstOK (#wits i)
        end

(* the partial results of the left-associated fold that planSet uses to
   combine a node's arguments *)
fun partialsOf lifted =
    let fun go (l, []) = [l]
          | go (l, acc) = acc @ [mk_lifted_union(List.last acc, l)]
    in
      List.foldl go [] lifted
    end

(* (t, |- set t <> ∅), when the composite isn't constant *)
fun planNontrivial plan =
    case plan of
        FPvar => let val a = mk_arb alpha in SOME (a, ISPEC a EQ_NONEMPTY) end
      | FPconst _ => NONE
      | FPnode {info = bI i, kids, ty} =>
        let
          val lifted =
              List.map (fn {set,sub,...} => mk_BIMGo (planSet sub, set)) kids
          val ps = partialsOf lifted
          val n = length kids
          fun climb (m, x, th) =
              (* th is about the m'th partial fold applied to x *)
              if m >= n then th
              else
                climb (m + 1, x,
                       MP (ISPECL [List.nth(ps, m-1), List.nth(lifted, m), x]
                                  LU_NONEMPTY1)
                          th)
          fun tryKid (j, kid as {set,sub,...} : fkid, inh) =
              case planNontrivial sub of
                  NONE => NONE
                | SOME (t, th) =>
                  let
                    val theta = match_type (type_of (#1 inh))
                                           (actual_of kid --> ty)
                    val x = mk_comb(Term.inst theta (#1 inh), t)
                    val inhth = SPEC t (INST_TYPE theta (#2 inh))
                    val base = MATCH_MP BIMGo_NONEMPTY (CONJ inhth th)
                    val atj =
                        if j = 1 then base
                        else MP (ISPECL [List.nth(ps, j-2),
                                         List.nth(lifted, j-1), x]
                                        LU_NONEMPTY2)
                                base
                  in
                    SOME (x, climb (j, x, atj))
                  end
          fun firstOK (_, [], _) = NONE
            | firstOK (j, k::ks, inh::inhs) =
              (case tryKid (j, k, inh) of
                   NONE => firstOK (j+1, ks, inhs)
                 | r => r)
            | firstOK _ = raise ERR "planNontrivial"
                                "no inhabits entry for a set function"
        in
          firstOK (1, kids, #inhabits i)
        end

(* ----------------------------------------------------------------------
    putting it together
   ---------------------------------------------------------------------- *)

fun fresh_tyvar avoid =
    let val cands = List.map mk_vartype ["'b","'c","'d","'e","'f","'g"]
    in
      case List.find (fn t => not (mem t avoid)) cands of
          SOME t => t
        | NONE => Type.gen_tyvar()
    end

type derived_bnf = {
  bnd : term,
  bndINFINITE : thm,
  bndthm : thm,
  components : info HOLset.set,
  mapCONG : thm,
  mapID : thm,
  mapIMAGE : thm,
  mapO : thm,
  mkmap : term -> term,
  nontrivial : (term * thm) option,
  set : term,
  wit : (term * thm) option
}

fun deriveBNF db ty : derived_bnf =
    let
      val plan = mkplan db ty
      val setA = planSet plan
      val tyvs = alpha :: type_vars ty
      val bty = fresh_tyvar tyvs
      val cty = fresh_tyvar (bty :: tyvs)
      val instB = Term.inst [alpha |-> bty]
      val f_ab = mk_var("f", alpha --> bty)
      val g_ab = mk_var("g", alpha --> bty)
      val f_bc = mk_var("f", bty --> cty)
      val (B, bndINF, bndthm) = planBnd plan
    in
      {bnd = B, bndINFINITE = bndINF, bndthm = bndthm,
       components = HOLset.addList(empty_biset, planInfos plan),
       mapCONG = planMapCONG (f_ab, g_ab) plan,
       mapID = planMapID plan,
       mapIMAGE = planMapIMAGE (f_ab, instB) plan,
       mapO = planMapO (f_bc, g_ab) plan,
       mkmap = planMap plan,
       nontrivial = planNontrivial plan,
       set = setA,
       wit = planWitness plan}
    end

end (* struct *)
