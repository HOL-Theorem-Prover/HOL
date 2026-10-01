Theory bnfDerive[bare]
Ancestors
  bnfPrelims
Libs
  HolKernel Parse boolLib bnfBase bnfLib testutils

(* Exercise bnfLib's derivation of the BNF structure of a composite
   functor built over the BNFs that bnfPrelims registers (sum, prod, fun
   and option).  In each type below, α is the functor's argument and all
   other type variables are constants. *)

val db = bnfBase.fullDB()

(* each example is paired with whether the composite should have an
   element whose set is empty.  It shouldn't when building an element
   forces you to supply the functor's argument: ‘:'b1 # 'a’ is the
   functor behind the (illegal) datatype fstream = FSCons 'b1 fstream,
   and ‘:one + 'b1 # 'a’ the one behind lists, where Nil is a witness. *)
val examples = [
  (* the functor's argument on its own *)
  (“:'a”, false),
  (* one component, argument used once *)
  (“:'a option”, true),
  (“:'b1 -> 'a”, false),
  (* argument used more than once, and at more than one depth *)
  (“:'a + 'a”, false),
  (“:'a # 'a option”, false),
  (“:('a # 'a) option”, true),
  (* argument-free positions *)
  (“:'b1 # 'a”, false),
  (“:one + 'b1 # 'a”, true),
  (“:'a + num”, true),
  (* the functor underlying the by-hand development in
     examples/bnf-datatypes/concreteBNF2Script.sml *)
  (“:'a1 + ('b1 -> ('a1 # 'a) option)”, true),
  (* deeper nestings, mixing all four component functors *)
  (“:(('a option # num) option + ('b1 -> 'a)) option”, true),
  (“:('b1 -> 'a) + num # ('b2 # 'a) option”, true),
  (“:('b1 -> ('b2 -> 'a option) # 'a) option + 'a”, true)
]

fun mk_IMAGE f =
    let val (d,r) = dom_rng (type_of f)
    in
      mk_comb(mk_thy_const{Thy = "pred_set", Name = "IMAGE",
                           Ty = (d --> r) --> ((d --> bool) --> (r --> bool))},
              f)
    end
fun mk_cardleq (l,r) =
    list_mk_icomb (prim_mk_const{Thy = "cardinal", Name = "cardleq"}, [l,r])

(* the derived theorems must be exactly the BNF laws for the map and set
   terms that were derived alongside them, and must not depend on any
   assumptions *)
fun lawsOK (d : bnfLib.derived_bnf) =
    let
      val {bnd,bndthm,mapCONG,mapID,mapIMAGE,mapO,mkmap,set,...} = d
      fun named th n =
          valOf (List.find (fn v => #1 (dest_var v) = n)
                           (free_vars (concl th)))
      val ty = #1 (dom_rng (type_of set))
      val x = mk_var("x", ty)
      val a = mk_var("a", alpha)
      fun I_of t = inst [alpha |-> t] combinSyntax.I_tm
      val oO = combinSyntax.mk_o

      val idOK = aconv (concl mapID) (mk_eq(mkmap (I_of alpha), I_of ty))

      val (f,g) = (named mapO "f", named mapO "g")
      val oOK = aconv (concl mapO)
                      (mk_eq(oO(mkmap f, mkmap g), mkmap (oO(f,g))))

      val fi = named mapIMAGE "f"
      val setrng = inst [alpha |-> #2 (dom_rng (type_of fi))] set
      val imgOK = aconv (concl mapIMAGE)
                        (mk_eq(oO(setrng, mkmap fi), oO(mk_IMAGE fi, set)))

      val (fc,gc) = (named mapCONG "f", named mapCONG "g")
      val congOK =
          aconv (concl mapCONG)
                (mk_imp(mk_forall(a,
                          mk_imp(pred_setSyntax.mk_in(a, mk_comb(set,x)),
                                 mk_eq(mk_comb(fc,a), mk_comb(gc,a)))),
                        mk_eq(mk_comb(mkmap fc, x), mk_comb(mkmap gc, x))))

      val bndOK = aconv (concl bndthm)
                        (mk_forall(x, mk_cardleq(mk_comb(set,x), bnd)))
    in
      List.all (null o hyp) [bndthm,mapCONG,mapID,mapIMAGE,mapO] andalso
      idOK andalso oOK andalso imgOK andalso congOK andalso bndOK
    end

(* the witness, when there is one, is an element of the composite's type
   whose set is empty; the nontriviality witness is one whose set isn't *)
fun witsOK haswit (d : bnfLib.derived_bnf) =
    let
      val {nontrivial,set,wit,...} = d
      val ty = #1 (dom_rng (type_of set))
      fun elemOK mk (t,th) =
          null (hyp th) andalso type_of t = ty andalso
          aconv (concl th) (mk (mk_comb(set,t), pred_setSyntax.mk_empty alpha))
    in
      (case wit of
           NONE => not haswit
         | SOME p => haswit andalso elemOK mk_eq p) andalso
      (case nontrivial of
           NONE => false
         | SOME p => elemOK (mk_neg o mk_eq) p)
    end

fun testty (ty,haswit) =
    (tprint ("deriveBNF " ^ type_to_string ty);
     require_msg (check_result (fn d => lawsOK d andalso witsOK haswit d))
                 (K "<derived BNF>")
                 (bnfLib.deriveBNF db) ty)

val _ = List.app (ignore o testty) examples

(* the map and set terms must agree with what functorToMapAndSet
   produces (the interface the by-hand developments use) *)
val _ =
    let
      val ty = “:'a1 + ('b1 -> ('a1 # 'a) option)”
      val (m,s,_) = bnfLib.functorToMapAndSet db ty
      val d = bnfLib.deriveBNF db ty
    in
      tprint "deriveBNF agrees with functorToMapAndSet";
      require_msg (check_result I) Bool.toString
                  (fn () => aconv m (#mkmap d (mk_var("f", alpha --> beta)))
                            andalso aconv s (#set d))
                  ()
    end

(* end to end: from a Datatype specification to the BNF of the functor
   whose fixed point the specified type would be.  The two specifications
   below are the standard example of the difference nonemptiness makes:
   ‘Cons 'a mylist’ alone leaves no way to build an element, so a
   witness has to come from another constructor. *)
fun specToFunctorTy q =
    case parse_bnf.parse2ftor (ParseDatatype.hparse (type_grammar()) q) of
        [(_,spec)] => bnfLib.specToFunctor spec
      | _ => raise Fail "expected a single type specification"

fun testspec (nm, q, expected_ty, haswit) =
    let
      val ty = specToFunctorTy q
      val _ = tprint ("Datatype spec " ^ nm)
    in
      require_msg (check_result (fn d => ty = expected_ty andalso
                                         lawsOK d andalso witsOK haswit d))
                  (K "<derived BNF>")
                  (bnfLib.deriveBNF db) ty
    end

val _ = List.app (ignore o testspec) [
      ("mylist", [QUOTE "mylist = Nil | Cons 'a mylist"],
       “:one + 'b1 # 'a”, true),
      ("fstrm", [QUOTE "fstrm = FSCons 'a fstrm"], “:'b1 # 'a”, false),
      ("btree", [QUOTE "btree = Lf 'a | Nd btree btree"],
       “:'b1 + 'a # 'a”, true),
      ("ftree", [QUOTE "ftree = Fnode ('a -> ftree option)"],
       “:'b1 -> 'a option”, true)
    ]

(* a composite must not use a type operator in a position it isn't
   functorial in *)
val _ =
    (tprint "deriveBNF rejects non-functorial position";
     require_msg (check_HOL_ERR (fn (s,f,_) => s = "bnfLib" andalso
                                                f = "mkplan"))
                 (K "<derived BNF>")
                 (bnfLib.deriveBNF db) “:'a -> num”)

Theorem bnfDerive_ran = boolTheory.TRUTH

(* ----------------------------------------------------------------------
    The n-ary derivation.  A functor with several arguments has one map
    taking a function per argument, and a set function, naturality
    theorem and bound per argument.
   ---------------------------------------------------------------------- *)

val a1 = mk_vartype "'a1"
val a2 = mk_vartype "'a2"
val b1 = mk_vartype "'b1"

fun lawsOKn lives (d : bnfLib.derived_bnfn) =
    let
      val {bnd,bndthms,mapCONG,mapID,mapIMAGE,mapO,mkmap,sets,...} = d
      val n = length lives
      fun named th nm =
          valOf (List.find (fn v => #1 (dest_var v) = nm)
                           (free_vars (concl th)))
      fun nmi base i = base ^ Int.toString (i + 1)
      val ty = #1 (dom_rng (type_of (hd sets)))
      val x = mk_var("x", ty)
      fun I_of t = inst [alpha |-> t] combinSyntax.I_tm
      val oO = combinSyntax.mk_o

      val idOK = aconv (concl mapID) (mk_eq(mkmap (map I_of lives), I_of ty))

      val fs = List.tabulate (n, fn i => named mapO (nmi "f" i))
      val gs = List.tabulate (n, fn i => named mapO (nmi "g" i))
      val oOK = aconv (concl mapO)
                      (mk_eq(oO(mkmap fs, mkmap gs),
                             mkmap (ListPair.map oO (fs,gs))))

      (* naturality, argument by argument *)
      val nfs = List.tabulate (n, fn i => named (hd mapIMAGE) (nmi "f" i))
      val theta = ListPair.map (fn (v,f) => v |-> #2 (dom_rng (type_of f)))
                               (lives, nfs)
      fun imgOK (i, th) =
          aconv (concl th)
                (mk_eq(oO(inst theta (List.nth (sets,i)), mkmap nfs),
                       oO(mk_IMAGE (List.nth (nfs,i)), List.nth (sets,i))))

      val cfs = List.tabulate (n, fn i => named mapCONG (nmi "f" i))
      val cgs = List.tabulate (n, fn i => named mapCONG (nmi "g" i))
      fun conghyp i =
          let val a = mk_var("a", List.nth (lives,i))
          in
            mk_forall(a,
              mk_imp(pred_setSyntax.mk_in(a, mk_comb(List.nth (sets,i), x)),
                     mk_eq(mk_comb(List.nth (cfs,i), a),
                           mk_comb(List.nth (cgs,i), a))))
          end
      val congOK =
          aconv (concl mapCONG)
                (mk_imp(list_mk_conj (List.tabulate (n, conghyp)),
                        mk_eq(mk_comb(mkmap cfs, x), mk_comb(mkmap cgs, x))))

      fun bndOK (i, th) =
          aconv (concl th)
                (mk_forall(x, mk_cardleq(mk_comb(List.nth (sets,i), x), bnd)))
    in
      List.all (null o hyp) ([mapCONG,mapID,mapO] @ mapIMAGE @ bndthms) andalso
      idOK andalso oOK andalso congOK andalso
      List.all imgOK (Lib.enumerate 0 mapIMAGE) andalso
      List.all bndOK (Lib.enumerate 0 bndthms)
    end

fun testtyn (lives, ty) =
    (tprint ("deriveBNFn " ^ type_to_string ty);
     require_msg (check_result (lawsOKn lives)) (K "<derived BNF>")
                 (bnfLib.deriveBNFn db lives) ty)

val _ = List.app (ignore o testtyn) [
      ([a1,a2], “:'a1 + 'a2”),
      ([a1,a2], “:one + 'a2 # 'a1”),
      ([a1,a2], “:('b1 -> 'a1) # 'a2 option”),
      ([a1,a2], “:('a1 # 'a2) option + 'b1 # 'a1”)
    ]

(* The laws relating one argument to another are instances of these, not
   separate obligations: setᵢ ignores what mapⱼ does because naturality
   for argument i puts IMAGE fᵢ on the right, and fᵢ can be I. *)
val _ = tprint "setᵢ ignores mapⱼ, as an instance of naturality"
val _ =
    let val d = bnfLib.deriveBNFn db [a1,a2] “:one + 'a2 # 'a1”
        val nat1 = hd (#mapIMAGE d)
        val set1 = hd (#sets d)
        fun findf th = valOf (List.find (fn v => #1 (dest_var v) = "f1")
                                        (free_vars (concl th)))
        (* put I in argument 1's position, whatever its target was named *)
        val bty = #2 (dom_rng (type_of (findf nat1)))
        val nat1' = INST_TYPE [bty |-> a1] nat1
        val I1 = inst [alpha |-> a1] combinSyntax.I_tm
        val x = mk_var("x", #1 (dom_rng (type_of set1)))
        (* the composition is unfolded only at the top: the set term is
           itself built out of o, and rewriting inside it would leave
           nothing recognisable *)
        val pw = CONV_RULE (RAND_CONV (REWR_CONV pred_setTheory.IMAGE_I))
                   (CONV_RULE (BINOP_CONV (REWR_CONV combinTheory.o_THM))
                      (AP_THM (INST [findf nat1' |-> I1] nat1') x))
        val (l,r) = dest_eq (concl pw)
    in
      (* what is left is set₁ (map f₂ I x) = set₁ x; on the left set₁ is
         at the instance f₂ moved argument 2 to *)
      if null (hyp pw) andalso aconv r (mk_comb(set1, x)) andalso
         can (match_term set1) (rator l)
      then OK()
      else die (thm_to_string pw)
    end

(* ----------------------------------------------------------------------
    Witnesses and inhabitation, in the form the database stores them: a
    witness takes one argument per live argument and its theorem records
    which of them it needed, and each argument has a term with an element
    of that argument inside it.  Registering a functor the package builds
    needs both in exactly this form.
   ---------------------------------------------------------------------- *)

fun witShapeOK lives (d : bnfLib.derived_bnfn) =
    let
      val n = length lives
      val {sets, wits, inhabits, ...} = d
      val ty = #1 (dom_rng (type_of (hd sets)))
      fun witOK (w, th) =
          let
            val args = #1 (strip_forall (concl th))
            val app = list_mk_comb (w, args)
            (* one argument per live argument, landing in the type *)
            val tyOK = null (free_vars w) andalso
                       length args = n andalso type_of app = ty andalso
                       ListPair.all (fn (a,v) => type_of a = v) (args, lives)
            fun conjOK (i, c) =
                let val (l, r) = pred_setSyntax.dest_subset c
                    val ai = List.nth (args, i)
                in
                  aconv l (mk_comb (List.nth (sets, i), app)) andalso
                  (pred_setSyntax.is_empty r orelse
                   aconv r (pred_setSyntax.mk_set [ai]))
                end
            val conjs = strip_conj (#2 (strip_forall (concl th)))
          in
            null (hyp th) andalso tyOK andalso length conjs = n andalso
            List.all conjOK (Lib.enumerate 0 conjs)
          end
      fun inhOK (_, NONE) = true
        | inhOK (i, SOME (t, th)) =
          let val v = #1 (dest_forall (concl th))
              val app = mk_comb (t, v)
          in
            null (hyp th) andalso null (free_vars t) andalso
            type_of t = (List.nth (lives, i) --> ty) andalso
            aconv (#2 (dest_forall (concl th)))
                  (pred_setSyntax.mk_in (v, mk_comb (List.nth (sets, i), app)))
          end
    in
      not (null wits) andalso List.all witOK wits andalso
      length inhabits = n andalso List.all inhOK (Lib.enumerate 0 inhabits)
    end

fun testwitn (lives, ty) =
    (tprint ("witnesses of " ^ type_to_string ty);
     require_msg (check_result (witShapeOK lives)) (K "<derived BNF>")
                 (bnfLib.deriveBNFn db lives) ty)

val _ = List.app (ignore o testwitn) [
      ([a1,a2], “:'a1 + 'a2”),
      ([a1,a2], “:one + 'a2 # 'a1”),
      ([a1,a2], “:('b1 -> 'a1) # 'a2 option”),
      ([a1,a2], “:('a1 # 'a2) option + 'b1 # 'a1”),
      ([alpha], “:one + 'b1 # 'a”),
      ([alpha], “:('a # 'a) option”)
    ]

(* which arguments the witnesses need is the whole point of keeping
   several of them: the functor behind ‘mylist = Nil | Cons 'a mylist’
   has one witness needing nothing (Nil), while every element of the one
   behind ‘fstrm = FSCons 'a fstrm’ needs both arguments *)
fun needsOf (d : bnfLib.derived_bnfn) =
    let fun sigOf (_, th) =
            List.map (not o pred_setSyntax.is_empty o #2 o
                      pred_setSyntax.dest_subset)
                     (strip_conj (#2 (strip_forall (concl th))))
    in
      List.map sigOf (#wits d)
    end

val _ = tprint "the witnesses' demands"
val _ =
    let
      val mylist = needsOf (bnfLib.deriveBNFn db [alpha,b1] “:one + 'b1 # 'a”)
      val fstrm = needsOf (bnfLib.deriveBNFn db [alpha,b1] “:'b1 # 'a”)
      val sum = needsOf (bnfLib.deriveBNFn db [a1,a2] “:'a1 + 'a2”)
    in
      if mylist = [[false,false]] andalso fstrm = [[true,true]] andalso
         sum = [[true,false],[false,true]]
      then OK()
      else die "unexpected demands"
    end
