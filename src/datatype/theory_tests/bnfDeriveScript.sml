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
