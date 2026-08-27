Theory bnfFixBNFTest
Ancestors
  bnfInitial bnfFixBNF bnfMoreFunctors pred_set cardinal
Libs
  HolKernel Parse boolLib bossLib bnfBase bnfLib bnfFixLib testutils

(* ----------------------------------------------------------------------
    fixpointBNF over a range of functors.

    What is checked, for each of them, is that the theorems derived are
    *exactly* the BNF laws for the map and set constants derived alongside
    them, that they are ground and hypothesis-free — a free variable would
    mean a parameter was never pinned down — and that the database accepts
    the result, since its sanity check is what catches a witness with a
    type variable the term doesn't have.  Then a functor is derived over
    the new type, which is what nested recursion needs.

    Several arguments matter here: the map takes one function per
    argument, the congruence is the chain of one-argument congruences, and
    the order the new type's operator takes its arguments in need not be
    the order the functor was derived in.
   ---------------------------------------------------------------------- *)

fun same t1 t2 = can (match_term t1) t2 andalso can (match_term t2) t1

fun mk_IMAGE f =
    let val (d,r) = dom_rng (type_of f)
    in
      mk_comb(mk_thy_const{Thy = "pred_set", Name = "IMAGE",
                           Ty = (d --> r) --> ((d --> bool) --> (r --> bool))},
              f)
    end
fun mk_cardleq (l,r) =
    list_mk_icomb (prim_mk_const{Thy = "cardinal", Name = "cardleq"}, [l,r])

(* the laws the database stores, as they must read for the map and set
   constants it stores alongside them *)
fun lawsOK (bnfBase.bI info) =
    let
      val {bnd,bndthms,map,mapCONG,mapID,mapIMAGE,mapO,set,canontype,
           wits,inhabits,...} = info
      val n = length set
      val lives = List.tabulate (n, fn i => mk_vartype ("'a" ^ Int.toString
                                                                 (i + 1)))
      val tgts = List.tabulate (n, fn i => mk_vartype ("'c" ^ Int.toString
                                                                 (i + 1)))
      val thirds = List.tabulate (n, fn i => mk_vartype ("'d" ^ Int.toString
                                                                  (i + 1)))
      fun numbered nm tys =
          List.tabulate (length tys,
                         fn i => mk_var(nm ^ Int.toString (i + 1),
                                        List.nth (tys, i)))
      val fs = numbered "f" (ListPair.map (op -->) (lives, tgts))
      val gs = numbered "g" (ListPair.map (op -->) (lives, tgts))
      val fs' = numbered "f" (ListPair.map (op -->) (tgts, thirds))
      fun I_of t = inst [alpha |-> t] combinSyntax.I_tm
      val oO = combinSyntax.mk_o
      fun theta (vs,tys) = ListPair.map (fn (v,t) => v |-> t) (vs, tys)
      fun setAt (srcs,i) = inst (theta (lives,srcs)) (List.nth (set, i))
      (* the map's own type variables, so that its instances can be built
         without assuming what they are called *)
      fun domains 0 _ = []
        | domains k ty = let val (d,r) = dom_rng ty in d :: domains (k-1) r end
      val margs = domains n (type_of map)
      val msrcs = List.map (#1 o dom_rng) margs
      val mtgts = List.map (#2 o dom_rng) margs
      fun mapAt hs =
          let val srcs = List.map (#1 o dom_rng o type_of) hs
              val tos = List.map (#2 o dom_rng o type_of) hs
          in
            list_mk_comb (inst (theta (msrcs,srcs) @ theta (mtgts,tos)) map,
                          hs)
          end
      val x = mk_var("x", canontype)

      val argsOK = msrcs = lives
      val idOK = same (concl mapID)
                      (mk_eq(mapAt (List.map I_of lives), I_of canontype))
      val oOK = same (concl mapO)
                     (mk_eq(oO(mapAt fs', mapAt gs),
                            mapAt (ListPair.map oO (fs',gs))))
      fun imgOK (i,th) =
          same (concl th)
               (list_mk_forall(fs @ [x],
                  mk_eq(mk_comb(setAt (tgts,i), mk_comb(mapAt fs, x)),
                        mk_comb(mk_IMAGE (List.nth (fs,i)),
                                mk_comb(setAt (lives,i), x)))))
      fun conghyp i =
          let val a = mk_var("a", List.nth (lives,i))
          in
            mk_forall(a,
              mk_imp(pred_setSyntax.mk_in(a, mk_comb(setAt (lives,i), x)),
                     mk_eq(mk_comb(List.nth (fs,i), a),
                           mk_comb(List.nth (gs,i), a))))
          end
      val congOK =
          same (concl mapCONG)
               (list_mk_forall(fs @ gs @ [x],
                  mk_imp(list_mk_conj (List.tabulate (n, conghyp)),
                         mk_eq(mk_comb(mapAt fs, x),
                               mk_comb(mapAt gs, x)))))
      fun bndOK (i,th) =
          same (concl th)
               (mk_forall(x, mk_cardleq(mk_comb(setAt (lives,i), x), bnd)))

      (* a witness takes one argument per argument of the functor and
         says, for each, whether it needed it *)
      fun witOK (w,th) =
          let
            val args = #1 (strip_forall (concl th))
            val app = list_mk_comb (w, args)
            fun conjOK (i,c) =
                let val (l,r) = pred_setSyntax.dest_subset c
                in
                  aconv l (mk_comb (setAt (lives,i), app)) andalso
                  (pred_setSyntax.is_empty r orelse
                   aconv r (pred_setSyntax.mk_set [List.nth (args, i)]))
                end
            val conjs = strip_conj (#2 (strip_forall (concl th)))
          in
            null (free_vars w) andalso length args = n andalso
            type_of app = canontype andalso length conjs = n andalso
            List.all conjOK (Lib.enumerate 0 conjs)
          end
      fun inhOK (i,(t,th)) =
          let val v = #1 (dest_forall (concl th))
          in
            null (free_vars t) andalso
            type_of t = (List.nth (lives,i) --> canontype) andalso
            aconv (#2 (dest_forall (concl th)))
                  (pred_setSyntax.mk_in
                     (v, mk_comb (setAt (lives,i), mk_comb (t, v))))
          end
    in
      List.all (null o hyp) ([mapID,mapO,mapCONG] @ mapIMAGE @ bndthms) andalso
      List.all (null o free_vars o concl) ([mapID,mapCONG] @ mapIMAGE @
                                           bndthms) andalso
      argsOK andalso idOK andalso oOK andalso congOK andalso
      List.all imgOK (Lib.enumerate 0 mapIMAGE) andalso
      List.all bndOK (Lib.enumerate 0 bndthms) andalso
      not (null wits) andalso List.all witOK wits andalso
      length inhabits = n andalso List.all inhOK (Lib.enumerate 0 inhabits)
    end

(* ----------------------------------------------------------------------
    the functors, and the type each becomes

    The Datatype specifications the functors come from are, in order:

      tlist = TNil | TCons 'b1 tlist
      tpair = PNil | PCons 'b1 'b2 tpair
      ttree = TLeaf 'b1 | TNode ttree ttree
      topt  = ONil | OCons ('b1 option) (topt option)
      tfm   = FM (num |-> tfm) | ND num (('b1 # tfm) list)

   the last of which recurses under a finite map and under a list, so its
   set function is a tower of the two.
   ---------------------------------------------------------------------- *)

val b1 = mk_vartype "'b1"
val b2 = mk_vartype "'b2"

val examples = [
  ("tlist", [alpha,b1], “:one + 'b1 # 'a”),
  ("tpair", [alpha,b1,b2], “:one + 'b1 # 'b2 # 'a”),
  ("ttree", [alpha,b1], “:'b1 + 'a # 'a”),
  (* an argument, and the recursion, under a registered functor: the map
     in the recursive argument alone is then not the identity on the
     parameter's position either *)
  ("topt", [alpha,b1], “:one + 'b1 option # 'a option”),
  (* recursion under two registered functors at once *)
  ("tfm", [alpha,b1], “:(num |-> 'a) + num # ('b1 # 'a) list”)
]

(* the database is threaded through: each type is added to it in memory
   as it is built, which is how a caller supplies the theorems the next
   step needs without anything being recorded *)
fun testty ((tyname, lives, ty), db) =
    let
      val bnf = deriveBNFn db lives ty
      val fix = defineFixpoint {tyname = tyname, ABS = tyname ^ "_ABS",
                                REP = tyname ^ "_REP"} bnf
      val res = fixpointBNF bnf fix
      val _ = tprint (tyname ^ " = " ^ type_to_string ty ^ " as a functor")
      val _ = if lawsOK (#info res) then OK()
              else die "the derived laws are not the map's"
      (* the database's sanity check is part of the test: a witness with a
         type variable its term doesn't pin down gets caught here *)
      val _ = tprint (tyname ^ " goes into a database")
    in
      (bnfBase.insert (#key res, #info res) db before OK())
      handle e => (die (General.exnMessage e); db)
    end

(* ----------------------------------------------------------------------
    and a functor over one of them, which is what nesting needs
   ---------------------------------------------------------------------- *)

val db = List.foldl testty (bnfBase.fullDB()) examples

val _ = tprint "a functor recursing under a two-argument fixed point"
val _ =
    let val d = deriveBNFn db [alpha,b1] “:one + ('b1, 'a) tpair”
    in
      if List.all (null o hyp)
                  ([#mapID d, #mapO d, #mapCONG d] @ #mapIMAGE d @ #bndthms d)
      then OK() else die "hypotheses left"
    end

(* the whole way: the recursive call arrives as the map of the type being
   recursed under *)
val _ = tprint "a datatype recursing under a two-argument fixed point"
val _ =
    let
      val d = deriveBNFn db [alpha,b1] “:one + ('b1, 'a) tpair”
      val fix = defineFixpoint {tyname = "prose", ABS = "prose_ABS",
                                REP = "prose_REP"} d
      val cs = defineConstructors ["PRLeaf", "PRNode"] d fix
    in
      if same (concl (#axiom cs))
              “∀f0 f1. ∃!h. h PRLeaf = f0 ∧
                            ∀a0. h (PRNode a0) = f1 a0 (tpairMAP I h a0)”
      then OK() else die (thm_to_string (#axiom cs))
    end
