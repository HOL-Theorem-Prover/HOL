Theory bnfDeriveFmap
Ancestors
  bnfPrelims finite_map list pred_set cardinal
Libs
  HolKernel Parse boolLib bossLib bnfBase bnfLib testutils

(* ----------------------------------------------------------------------
    deriveBNF over functors that recurse through finite maps and lists.
    The first example is the functor from concreteBNFScript.sml, written
    with the recursion argument as α and the passive argument as 'b1.
   ---------------------------------------------------------------------- *)

val db = bnfBase.fullDB()

val examples = [
  (* concreteBNFScript's F : (num |-> β) + num # (α # β) list *)
  (“:(num |-> 'a) + num # ('b1 # 'a) list”, true),
  (* recursion under a finite map alone, and under a list alone *)
  (“:'b1 |-> 'a”, true),
  (“:'a list”, true),
  (* the map's domain is itself a parameter *)
  (“:one + 'b1 # ('b2 |-> 'a)”, true),
  (* nested: a list of finite maps of lists *)
  (“:('b1 |-> 'a list) list”, true),
  (* recursion under a function and an option: NONE gives an element of
     the option without needing an α, so K NONE witnesses the function *)
  (“:('b1 -> ('b2 |-> 'a) option) + 'a # 'a”, true),
  (* and with the option removed, K FEMPTY still gives a function
     without needing an α *)
  (“:('b1 -> ('b2 |-> 'a)) + 'a # 'a”, true),
  (* a finite map of pairs where the other component recurses too *)
  (“:'b1 |-> ('a # 'a list)”, true)
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
      val (f,g) = (named mapO "f", named mapO "g")
      val fi = named mapIMAGE "f"
      val setrng = inst [alpha |-> #2 (dom_rng (type_of fi))] set
      val (fc,gc) = (named mapCONG "f", named mapCONG "g")
    in
      List.all (null o hyp) [bndthm,mapCONG,mapID,mapIMAGE,mapO] andalso
      aconv (concl mapID) (mk_eq(mkmap (I_of alpha), I_of ty)) andalso
      aconv (concl mapO) (mk_eq(oO(mkmap f, mkmap g), mkmap (oO(f,g)))) andalso
      aconv (concl mapIMAGE)
            (mk_eq(oO(setrng, mkmap fi), oO(mk_IMAGE fi, set))) andalso
      aconv (concl mapCONG)
            (mk_imp(mk_forall(a,
                      mk_imp(pred_setSyntax.mk_in(a, mk_comb(set,x)),
                             mk_eq(mk_comb(fc,a), mk_comb(gc,a)))),
                    mk_eq(mk_comb(mkmap fc, x), mk_comb(mkmap gc, x)))) andalso
      aconv (concl bndthm) (mk_forall(x, mk_cardleq(mk_comb(set,x), bnd)))
    end

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

Theorem bnfDeriveFmap_ran = boolTheory.TRUTH
