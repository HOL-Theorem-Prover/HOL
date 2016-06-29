(*---------------------------------------------------------------------------*
 * Theory of pairs and associated support.                                   *
 *---------------------------------------------------------------------------*)

structure pairLib :> pairLib =
struct

local open pairTheory pairSimps pairTools PairRules in end;

open HolKernel boolLib pairSyntax PairedLambda pairTools simpLib;

fun pairLib_ERR src msg = mk_HOL_ERR "pairLib" src msg

val _ = Rewrite.add_implicit_rewrites pairTheory.pair_rws;

(* Implementation of new_specification as a rule derived from
   gen_new_specification. This occurs here because the derivation
   depends on pairs. *)

(* given (λ(x,y,...) ...) arg                            (UOK)
  produces an assumption:
  arg = (x,y,...)
  where the variables may be primed if necessary *)
fun split_uncurry_arg_tac tm =
  let
    val (f,p) = dest_comb tm
    val (x,b) = pairSyntax.dest_pabs f
    val (x,s) = variant_of_term (free_vars p) x
    val xs = pairSyntax.strip_pair x
    val g = list_mk_exists(xs,mk_eq(p,x))
    (* ?x y z ... .  arg = (x,y,z,...) *)
    val th =
        prove(g, simpLib.SIMP_TAC boolSimps.bool_ss
                                  [GSYM pairTheory.EXISTS_PROD])
  in
    strip_assume_tac th
  end

local
  val find_and_split_pair =
      partial(pairLib_ERR"find_and_split_pair""not found")
             (bvk_find_term
                (fn (ls,tm) =>
                    is_comb tm andalso
                    List.all (not o
                              curry HOLset.member(FVL[rand tm]empty_tmset)) ls)
                split_uncurry_arg_tac)
in
val pairarg_tac =
    (fn g => find_and_split_pair (#2 g) g) ORELSE
    first_assum(find_and_split_pair o concl)
end (* local *)

local
  exception Not_pair_case
  fun loop tm vs =
    let
      val _ = assert is_pair_case tm
      val (f,x) = dest_comb tm
    in
      let
        val (v,b) = dest_abs x
        val vs = v::vs
      in
        case total dest_abs b of
          NONE => (vs,tm)
        | SOME (v,tm) => loop tm vs
          handle Not_pair_case => (v::vs,tm)
      end handle HOL_ERR _ => (vs,tm)
    end handle HOL_ERR _ => raise Not_pair_case
in
fun strip_pair_case tm =
    (case loop tm [] of (vs,b) => (lhand tm,rev vs,b))
    handle Not_pair_case =>
           raise pairLib_ERR "strip_pair_case" "not a pair case"

fun split_pair_case0_tac tm =
  let
    open boolSimps simpLib
    val (p,vs,b) = strip_pair_case tm
    val vs = map (variant (free_vars p)) vs
    val g = list_mk_exists(vs,mk_eq(p,pairSyntax.list_mk_pair vs))
    val th = prove(g, SIMP_TAC bool_ss [GSYM pairTheory.EXISTS_PROD])
  in
    strip_assume_tac th
  end
end (* local *)


local
open pairSyntax
fun find_split t g =
      partial(pairLib_ERR"split_pair_case_tac" "not found")
        (bvk_find_term
           (fn (ls,tm) =>
               is_pair_case tm andalso
               let val fvs = FVL [lhand tm] empty_tmset
               in
                 List.all (fn bv => not(HOLset.member(fvs,bv))) ls
               end)
           split_pair_case0_tac) t g
in
fun split_pair_case_tac (g as (_,w)) =
  (find_split w ORELSE first_assum (find_split o concl)) g

end (* local *)

local
  open Term Thm

  (* given a varstruct (possibly nested pairs of variables) vs, return a list
     of equations equating each variable to the corresponding projection of tm
     e.g. varstruct_to_eqs tm ((p,q),r) =
          [r = SND tm,
           q = SND (FST tm),
           p = FST (FST tm)] *)
  fun varstruct_to_eqs tm =
    let
      fun f tm ac vs =
        if is_var vs
          then (mk_eq(vs, tm))::ac
        else
          let
            val (a,d) = dest_pair vs
            val ac = f (mk_fst tm) ac a
            val ac = f (mk_snd tm) ac d
          in ac end
    in
      f tm []
    end

  val strip_n_exists =
    let
      fun f a n tm =
        if n = 0 then (List.rev a,tm)
        else let
          val (x,tm) = dest_exists tm
        in
          f (x::a) (n-1) tm
        end
    in f [] end

  fun nconv 0 c = ALL_CONV
    | nconv 1 c = c
    | nconv n c = c THENC (nconv (n-1) c)

  open Lib PairRules pairSyntax

  in

  fun new_specification (name,cnames,th) = let
    val n = List.length cnames in if n = 0 then
      Theory.Definition.gen_new_specification (name,th)
    else let
    val th1 =
      (* CONV_RULE (RENAME_VARS_CONV cnames) th
         is not good enough since it doesn't guarantee the cnames will be used
        - primed variants could be used if they clash with existing constant names
      *)
      let
        val tm1 = concl th
        val (vs1,body1) = strip_n_exists n tm1
        val tys = map type_of vs1
        val vs2 = map2 (curry mk_var) cnames tys
        val body2 = Term.subst (map2 (curry op |->) vs1 vs2) body1
        val tm2 = list_mk_exists(vs2,body2)
        val th2 = ALPHA tm1 tm2
      in EQ_MP th2 th end
    (* turn it into a single paired existential *)
    val th2 = CONV_RULE (nconv (n-1) UNCURRY_EXISTS_CONV) th1
    val (vs,body) = dest_pexists (concl th2)
    val witness = mk_pselect (vs,body)
    val eqs = varstruct_to_eqs witness vs
    val th3 = CONV_RULE PEXISTS_CONV th2
    val th4 = PURE_REWRITE_RULE (List.map (SYM o ASSUME) eqs) th3
    (* ensure that even totally unconstrained constants get defined *)
    val th5 = List.foldl (Lib.uncurry ADD_ASSUM) th4 eqs
    in
      Theory.Definition.gen_new_specification (name,th5)
    end end

end

val add_pair_compset = computeLib.add_thms
  (List.map computeLib.lazyfy_thm
     let open pairTheory in
       [CLOSED_PAIR_EQ,FST,SND,pair_case_thm,SWAP_def,
        CURRY_DEF,UNCURRY_DEF,PAIR_MAP_THM]
     end)

val () = add_pair_compset computeLib.the_compset

end
