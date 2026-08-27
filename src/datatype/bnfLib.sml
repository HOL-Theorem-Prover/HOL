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

(* The functor may have several arguments, so the element type of a set
   function is a parameter here rather than always α: setᵢ collects the
   occurrences of argument i, and an occurrence of any other argument
   contributes nothing to it. *)
fun equal_ty ty = Term.inst [alpha |-> ty] boolSyntax.equality
(* K (∅ : elem set) : dom -> elem set *)
fun K0e elem dom =
    combinSyntax.mk_K_1 (pred_setSyntax.mk_empty elem, dom)
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

fun mk_lifted_union (f1,f2) =
    (* f1 and f2 have the same type, some domain → elem set; generate
       S ((UNION) o f1) f2 *)
    let
      val (b,setty) = dom_rng (type_of f1)
      val UNION_e = mk_thy_const{Thy = "pred_set", Name = "UNION",
                                 Ty = setty --> (setty --> setty)}
      val Uof1 = combinSyntax.mk_o(UNION_e, f1)
      val Stm = mk_thy_const{Thy = "combin", Name = "S",
                             Ty = (b --> (setty --> setty)) -->
                                  ((b --> setty) --> (b --> setty))}
    in
      list_mk_comb(Stm, [Uof1, f2])
    end

(* BIMG f o set *)
fun mk_BIMGo (f, set) =
    let val (fd, fr) = dom_rng (type_of f)
        val elem = #1 (dom_rng fr)
    in
      combinSyntax.mk_o(mk_comb(inst [alpha |-> elem, beta |-> fd] BIMG, f),
                        set)
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
    FPvar of int * hol_type (* the functor's i-th argument, and its type *)
  | FPconst of hol_type     (* an argument-free type; the constant functor *)
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

fun idxOf lives ty =
    let fun go _ [] = NONE
          | go i (v::vs) = if v = ty then SOME i else go (i + 1) vs
    in
      go 0 lives
    end
fun livesIn lives ty = List.exists (fn v => mem v (type_vars ty)) lives

fun mkplan db lives ty =
    case idxOf lives ty of
        SOME i => FPvar (i, ty)
      | NONE =>
    if not (livesIn lives ty) then FPconst ty
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
                  else if livesIn lives a then
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
                    val sub = if livesIn lives actual then
                                mkplan db lives actual
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

fun planMap lives plan fs =
    case plan of
        FPvar (i,_) => List.nth (fs, i)
      | FPconst ty => Ityped ty
      | FPnode {info = bI i, kids, ty, ...} =>
        let
          val submaps = List.map (fn {sub,...} => planMap lives sub fs) kids
          val theta = ListPair.mapEq
                        (fn (v,f) => v |-> #1 (dom_rng (type_of f)))
                        (lives, fs)
          val srcty = type_subst theta ty
        in
          apply_map (#map i) submaps srcty
        end

(* the set function for the functor's i-th argument *)
fun planSet lives i plan =
    let val vi = List.nth (lives, i)
    in
      case plan of
          FPvar (j, ty) => if i = j then equal_ty vi else K0e vi ty
        | FPconst ty => K0e vi ty
        | FPnode {kids, ...} =>
          let
            fun lift ({set,sub,...}:fkid) =
                mk_BIMGo (planSet lives i sub, set)
            val lifted = List.map lift kids
          in
            List.foldl (fn (t,A) => mk_lifted_union(A,t))
                       (hd lifted) (tl lifted)
          end
    end

(* the type the plan describes.  Reading it off a set term, as this
   used to, built the whole BIMG/union term just to project its
   domain. *)
fun planTy plan =
    case plan of
        FPvar (_,ty) => ty
      | FPconst ty => ty
      | FPnode {ty,...} => ty

fun planInfos plan =
    case plan of
        FPvar _ => []
      | FPconst _ => []
      | FPnode {info, kids, ...} =>
        info :: List.concat (List.map (planInfos o #sub) kids)

fun functorToMapAndSet db ty =
    let val plan = mkplan db [alpha] ty
    in
      (planMap [alpha] plan [map_f], planSet [alpha] 0 plan,
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

val num_ty = numSyntax.num
val list_mk_sumty = sumSyntax.list_mk_sum

fun planBndTypes plan =
    case plan of
        FPvar _ => []
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

fun planBndThm lives i (B, Bne, Binf, bndtys) plan =
    let val st = planSet lives i plan
        val x = mk_var("x", #1 (dom_rng (type_of st)))
        val goal = mk_forall(x, mk_cardleq(mk_comb(st,x), B))
    in
      case plan of
          FPvar (j,_) =>
            if i = j then inst_forall (MATCH_MP EQ_CARDLE Bne) goal
            else inst_forall K0_CARDLE goal
        | FPconst _ => inst_forall K0_CARDLE goal
        | FPnode {kids, ...} =>
          let
            fun kidthm ({set,bnd,bndthm,sub}:fkid) =
                let
                  val subth = planBndThm lives i (B,Bne,Binf,bndtys) sub
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

fun planBnd lives plan =
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
      (B, Binf,
       List.tabulate (length lives,
                      fn i => planBndThm lives i (B, Bne, Binf, tys) plan))
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

fun planMapID lives plan =
    case plan of
        FPvar (_,ty) => REFL (Ityped ty)
      | FPconst ty => REFL (Ityped ty)
      | FPnode {info = bI i, kids, ...} =>
        let
          val kidths = List.map (planMapID lives o #sub) kids
          val hdtm = #1 (strip_comb
                           (planMap lives plan (List.map Ityped lives)))
          val cong =
              List.foldl (fn (kth,A) => MK_COMB(A,kth)) (REFL hdtm) kidths
        in
          TRANS cong (inst_lhs (#mapID i) (rhs (concl cong)))
        end

fun planMapO lives (fs,gs) plan =
    case plan of
        FPvar (i,_) => REFL (combinSyntax.mk_o(List.nth (fs,i),
                                               List.nth (gs,i)))
      | FPconst ty => CONJUNCT1 (ISPEC (Ityped ty) combinTheory.I_o_ID)
      | FPnode {info = bI i, kids, ...} =>
        let
          val step1 = inst_lhs (#mapO i)
                        (combinSyntax.mk_o(planMap lives plan fs,
                                           planMap lives plan gs))
          val kidths = List.map (planMapO lives (fs,gs) o #sub) kids
          val hdtm = #1 (strip_comb (rhs (concl step1)))
          val step2 = List.foldl (fn (kth,A) => MK_COMB(A,kth)) (REFL hdtm)
                                 kidths
        in
          TRANS step1 step2
        end

(* naturality for the i-th argument: an occurrence of another argument
   contributes nothing to setᵢ, so it is handled exactly like a constant
   — with that argument's own function in place of I *)
fun planMapIMAGE lives i (fs, instB) plan =
    let val f = List.nth (fs, i)
        val vi = List.nth (lives, i)
        fun constcase mp dom =
            inst_thm K0_natural
                     (mk_eq(combinSyntax.mk_o(instB (K0e vi dom), mp),
                            combinSyntax.mk_o(mk_IMAGE f, K0e vi dom)))
    in
    case plan of
        FPvar (j,ty) => if i = j then ISPEC f EQ_natural
                        else constcase (List.nth (fs,j)) ty
      | FPconst ty => constcase (Ityped ty) ty
      | FPnode {info = bI inf, kids, ...} =>
        let
          val mp = planMap lives plan fs
          fun kidthm (({set,sub,...}:fkid), imgth) =
              MATCH_MP BIMG_o_natural
                       (CONJ (inst_lhs (mapIMG_ofy imgth)
                                       (combinSyntax.mk_o(instB set, mp)))
                             (planMapIMAGE lives i (fs,instB) sub))
          val kths = ListPair.mapEq kidthm (kids, #mapIMAGE inf)
        in
          List.foldl (fn (t,A) => MATCH_MP LU_natural (CONJ A t))
                     (hd kths) (tl kths)
        end
    end

(* the hypothesis of the composite's congruence theorem talks about the
   whole of the composite's set; break it up into the parts that the
   node's own congruence theorem needs *)
fun splitLU th n =
    if n <= 1 then [th]
    else
      let val p = MATCH_MP LU_CONG_hyp th
      in splitLU (CONJUNCT1 p) (n - 1) @ [CONJUNCT2 p] end

fun planMapCONG lives (fs,gs) plan =
    let
      val n = length lives
      val sets = List.tabulate (n, fn i => planSet lives i plan)
      val ty = #1 (dom_rng (type_of (hd sets)))
      val x = mk_var("x", ty)
      fun hypOf i =
          let val a = mk_var("a", List.nth (lives, i))
          in
            mk_forall(a,
              mk_imp(pred_setSyntax.mk_in(a, mk_comb(List.nth (sets,i), x)),
                     mk_eq(mk_comb(List.nth (fs,i), a),
                           mk_comb(List.nth (gs,i), a))))
          end
      val hyp = list_mk_conj (List.tabulate (n, hypOf))
      val parts = CONJUNCTS (ASSUME hyp)
    in
      case plan of
          FPvar (i,_) =>
            DISCH hyp
              (MP (ISPECL [List.nth (fs,i), List.nth (gs,i), x] EQ_CONG)
                  (List.nth (parts, i)))
        | FPconst _ => DISCH hyp (REFL (mk_comb(Ityped ty, x)))
        | FPnode {info = bI inf, kids, ...} =>
          let
            (* each argument's hypothesis is about a union over the node's
               own arguments, so it splits the same way *)
            val splits = List.map (fn p => splitLU p (length kids)) parts
            fun kidfact (k, ({set,sub,...}:fkid)) =
                let
                  val sty = planTy sub
                  val y = mk_var("y", sty)
                  val ymem = pred_setSyntax.mk_in(y, mk_comb(set, x))
                  val subhyps =
                      List.map (fn sp => MATCH_MP BIMG_o_CONG_hyp
                                           (CONJ (List.nth (sp,k))
                                                 (ASSUME ymem)))
                               splits
                  val ih = INST [mk_var("x", sty) |-> y]
                                (planMapCONG lives (fs,gs) sub)
                in
                  GEN y (DISCH ymem (MP ih (LIST_CONJ subhyps)))
                end
            val facts = List.tabulate
                          (length kids,
                           fn k => kidfact (k, List.nth (kids, k)))
          in
            DISCH hyp (MATCH_MP (GEN_ALL (#mapCONG inf)) (LIST_CONJ facts))
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

fun actual_of ({sub,...}:fkid) = planTy sub

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
fun planWitness lives i plan =
    let val vi = List.nth (lives, i)
        fun constwit ty =
            let val w = mk_arb ty
            in
              SOME (w, inst_thm K0_EMPTY
                                (mk_eq(mk_comb(K0e vi ty, w),
                                       pred_setSyntax.mk_empty vi)))
            end
    in
    case plan of
        FPvar (j,ty) => if i = j then NONE else constwit ty
      | FPconst ty => constwit ty
      | FPnode {info = bI inf, kids, ty} =>
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
                      case planWitness lives i sub of
                          NONE => NONE
                        | SOME (t,th) => SOME (t, MATCH_MP SING_ALL th)
                    else
                      SOME (mk_arb (actual_of kid),
                            ISPEC (planSet lives i sub) EMPTY_ALL)
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
          firstOK (#wits inf)
        end
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
fun planNontrivial lives i plan =
    case plan of
        FPvar (j,ty) =>
          if i = j then let val a = mk_arb ty
                        in SOME (a, ISPEC a EQ_NONEMPTY) end
          else NONE
      | FPconst _ => NONE
      | FPnode {info = bI inf, kids, ty} =>
        let
          fun lift ({set,sub,...}:fkid) =
              mk_BIMGo (planSet lives i sub, set)
          val lifted = List.map lift kids
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
              case planNontrivial lives i sub of
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
          firstOK (1, kids, #inhabits inf)
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

(* the same thing for a functor with several arguments: one map taking a
   function per argument, and one set function, naturality theorem and
   bound per argument.  The cross-laws between different arguments —
   setᵢ (mapⱼ f x) = setᵢ x, and the commutation of mapᵢ with mapⱼ — are
   instances of these, not extra obligations: put I in the other
   positions of mapIMAGE and mapO. *)
type derived_bnfn = {
  bnd : term,
  bndINFINITE : thm,
  bndthms : thm list,
  components : info HOLset.set,
  lives : hol_type list,
  mapCONG : thm,
  mapID : thm,
  mapIMAGE : thm list,
  mapO : thm,
  mkmap : term list -> term,
  nontrivial : (term * thm) option list,
  sets : term list,
  wits : (term * thm) option list
}

fun deriveBNFn db lives ty : derived_bnfn =
    let
      val plan = mkplan db lives ty
      val n = length lives
      val tyvs = lives @ type_vars ty
      (* one fresh target variable per argument, and one more for mapO's
         middle stage *)
      fun freshes 0 avoid acc = (List.rev acc, avoid)
        | freshes k avoid acc =
          let val t = fresh_tyvar avoid
          in freshes (k-1) (t::avoid) (t::acc) end
      val (bs, avoid1) = freshes n tyvs []
      val (cs, _) = freshes n avoid1 []
      val instB = Term.inst (ListPair.mapEq (fn (a,b) => a |-> b) (lives, bs))
      (* numbered, because same-named variables at different types print
         identically and are impossible to read *)
      fun numbered nm tys =
          List.tabulate (length tys,
                         fn i => mk_var(if n = 1 then nm
                                        else nm ^ Int.toString (i + 1),
                                        List.nth (tys, i)))
      val fs_ab = numbered "f" (ListPair.mapEq (op -->) (lives, bs))
      val gs_ab = numbered "g" (ListPair.mapEq (op -->) (lives, bs))
      val fs_bc = numbered "f" (ListPair.mapEq (op -->) (bs, cs))
      val (B, bndINF, bndthms) = planBnd lives plan
    in
      {bnd = B, bndINFINITE = bndINF, bndthms = bndthms,
       components = HOLset.addList(empty_biset, planInfos plan),
       lives = lives,
       mapCONG = planMapCONG lives (fs_ab, gs_ab) plan,
       mapID = planMapID lives plan,
       mapIMAGE = List.tabulate
                    (n, fn i => planMapIMAGE lives i (fs_ab, instB) plan),
       mapO = planMapO lives (fs_bc, gs_ab) plan,
       mkmap = planMap lives plan,
       nontrivial = List.tabulate (n, fn i => planNontrivial lives i plan),
       sets = List.tabulate (n, fn i => planSet lives i plan),
       wits = List.tabulate (n, fn i => planWitness lives i plan)}
    end

(* the one-argument view, which is what the fixed-point construction
   consumes *)
fun deriveBNF db ty : derived_bnf =
    let val b = deriveBNFn db [alpha] ty
    in
      {bnd = #bnd b, bndINFINITE = #bndINFINITE b, bndthm = hd (#bndthms b),
       components = #components b, mapCONG = #mapCONG b, mapID = #mapID b,
       mapIMAGE = hd (#mapIMAGE b), mapO = #mapO b,
       mkmap = (fn f => #mkmap b [f]),
       nontrivial = hd (#nontrivial b), set = hd (#sets b),
       wit = hd (#wits b)}
    end

end (* struct *)
