(*---------------------------------------------------------------------------*
 * Theory of pairs and associated support.                                   *
 *---------------------------------------------------------------------------*)

structure pairLib :> pairLib =
struct

local open pairTheory pairSimps pairTools PairRules in end;

open boolLib pairSyntax PairedLambda pairTools simpLib;

val _ = Rewrite.add_implicit_rewrites pairTheory.pair_rws;

(* Implementation of new_specification as a rule derived from
   gen_new_specification. This occurs here because the derivation
   depends on pairs. *)

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
