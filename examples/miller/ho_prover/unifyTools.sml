structure unifyTools :> unifyTools =
struct

open HolKernel Parse boolLib;

open hurdUtils;

infixr 0 oo ## ++ << || THENC ORELSEC THENR ORELSER;
infix 1 >> |->;

val op++ = op THEN;
val op<< = op THENL;
val op|| = op ORELSE;
val op>> = op THEN1;
val !! = REPEAT;

val assert = simple_assert;

(* ------------------------------------------------------------------------- *)
(* Type unification.                                                         *)
(* ------------------------------------------------------------------------- *)

local
  fun is_tyvar vars ty = is_vartype ty andalso mem ty vars

  fun occurs tv ty = mem tv (type_vars ty)

  fun solve _ sub [] = sub
    | solve vars sub (tys :: rest) =
    solve' vars sub (Df (type_inst sub) tys) rest
  and solve' vars sub (ty1, ty2) rest =
    if is_tyvar vars ty1 then
      if ty1 = ty2 then solve vars sub rest
      else if occurs ty1 ty2 then raise ERR "type_unify" "occurs check"
      else
        (case total (find_redex ty1) sub of NONE
           => solve vars (type_refine_subst sub [ty1 |-> ty2]) rest
         | SOME {residue, ...}
           => solve' vars sub (ty2, residue) rest)
    else if is_tyvar vars ty2 then solve' vars sub (ty2, ty1) rest
    else if is_vartype ty1 then
      let
        val _ = assert (ty1 = ty2) (ERR "type_unify" "(vartype, non-vartype)")
      in
        solve vars sub rest
      end
    else
      let
        val (ty2_n, ty2_a) = dest_type ty2
        val (ty1_n, ty1_a) = dest_type ty1
        val _ = assert (ty1_n = ty2_n)
          (ERR "type_unify" "different type constructors")
      in
        solve vars sub (zip ty1_a ty2_a @ rest)
      end
in
  fun var_type_unify vars ty1 ty2 = solve' vars [] (ty1, ty2) []
end;

fun type_unify ty1 ty2 =
  var_type_unify (union (type_vars ty1) (type_vars ty2)) ty1 ty2;

fun sep_var_type_unify (vars1, ty1) (vars2, ty2) =
  let
    val (gvars1, (old_to_new1, new_to_old1)) = type_new_vars vars1
    val (gvars2, (old_to_new2, new_to_old2)) = type_new_vars vars2
    val ty1' = type_inst old_to_new1 ty1
    val ty2' = type_inst old_to_new2 ty2
    val sub = var_type_unify (gvars1 @ gvars2) ty1' ty2'
    val (sub1, sub2) = partition (C mem gvars1 o redex) sub
    val renaming_sub = new_to_old1 @ new_to_old2
  in
    Df (clean_subst o subst_map (D (type_inst renaming_sub))) (sub1, sub2)
  end;

fun sep_type_unify ty1 ty2 =
  sep_var_type_unify (type_vars ty1, ty1) (type_vars ty2, ty2);

(*
ff2 type_unify ``:'fred -> 'fred`` ``:'fred``;
tt2 sep_type_unify ``:'fred -> 'fred`` ``:'fred``;
tt2 sep_var_type_unify ([], ``:'fred -> 'fred``) ([``:'fred``], ``:'fred``);
ff2 sep_var_type_unify ([``:'fred``], ``:'fred -> 'fred``) ([], ``:'fred``);
tt2 type_unify ``:'a -> 'a -> 'b`` ``:bool -> 'c -> 'c``;
ff3 var_type_unify [``:'a``, ``:'b``] ``:'a -> 'a -> 'b`` ``:bool -> 'c -> 'c``;
tt3 var_type_unify [``:'a``, ``:'b``, ``:'c``] ``:'a -> 'a -> 'b``
  ``:bool -> 'c -> 'c``;
ff2 type_unify ``:'a list -> 'a list -> 'b`` ``:bool list -> 'a -> 'a``;
tt2 sep_type_unify ``:'a list -> 'a list -> 'b`` ``:bool list -> 'a -> 'a``;
ff2 sep_var_type_unify ([``:'a``], ``:'a list -> 'a list -> 'b``)
  ([``:'a``], ``:bool list -> 'a -> 'a``);
tt2 sep_var_type_unify ([``:'a``, ``:'b``], ``:'a list -> 'a list -> 'b``)
  ([``:'a``], ``:bool list -> 'a -> 'a``);
tt2 type_unify ``:'a -> 'b`` ``:bool -> 'b``;
tt3 var_type_unify [``:'a``] ``:'a -> 'b`` ``:bool -> 'b``;
tt2 sep_var_type_unify ([``:'a``], ``:'a -> 'b``) ([], ``:bool -> 'b``);
tt2 sep_type_unify ``:'a -> 'b`` ``:bool -> 'b``;
*)

(* ------------------------------------------------------------------------- *)
(* First-order unification.                                                  *)
(* ------------------------------------------------------------------------- *)
fun tdistinct tl = HOLset.numItems (listset tl) = length tl
fun mk_renaming_tsubst_wrt_vars vars sub =
  let
    val (ok_sub, problem_sub) = partition (C tmem vars o redex) sub
    val problem_sub_residues = map residue problem_sub
    val _ = assert (forall (C tmem vars) problem_sub_residues)
      (ERR "rename_sub_for_vars" "have not_var |-> not_var")
    val _ = assert (tdistinct problem_sub_residues)
      (ERR "rename_sub_for_vars" "have two not_vars |-> same_var")
    val ok_sub_redexes = map redex ok_sub
    val _ = assert (forall (not o C tmem ok_sub_redexes) problem_sub_residues)
      (ERR "rename_sub_for_vars" "have not_var |-> used_var")
    val problem_sub_redexes = map redex problem_sub
  in
    zipwith (curry op|->) problem_sub_residues problem_sub_redexes
  end;

fun mk_renaming_subst_wrt_vars vars sub =
  let
    val (ok_sub, problem_sub) = partition (C mem vars o redex) sub
    val problem_sub_residues = map residue problem_sub
    val _ = assert (forall (C mem vars) problem_sub_residues)
      (ERR "rename_sub_for_vars" "have not_var |-> not_var")
    val _ = assert (distinct problem_sub_residues)
      (ERR "rename_sub_for_vars" "have two not_vars |-> same_var")
    val ok_sub_redexes = map redex ok_sub
    val _ = assert (forall (not o C mem ok_sub_redexes) problem_sub_residues)
      (ERR "rename_sub_for_vars" "have not_var |-> used_var")
    val problem_sub_redexes = map redex problem_sub
  in
    zipwith (curry op|->) problem_sub_residues problem_sub_redexes
  end;

local
  fun unify_reduce_ty ty1 ty2 sub = refine_subst sub ([], type_unify ty1 ty2)

  fun occurs v tm = free_in v tm

  fun solve sub [] = sub
    | solve (sub as (_, ty_sub)) (((bvs1, tm1), (bvs2, tm2)) :: rest) =
    let
      val (bvs1', bvs2') = Df (map (inst_ty ty_sub)) (bvs1, bvs2)
      val (tm1', tm2') = Df (pinst sub) (tm1, tm2)
    in
      solve' sub ((bvs1', tm1'), (bvs2', tm2')) rest
    end
  and solve' sub ((bvs1, tm1), (bvs2, tm2)) rest =
    if is_bv bvs1 tm1 orelse is_bv bvs2 tm2 then
      let
        val _ = assert (dest_bv bvs1 tm1 = dest_bv bvs2 tm2)
          (ERR "unify" "different bound vars do not match")
      in
        solve sub rest
      end
    else if is_var tm1 then
      let
        val bvfvs = FVs tm2 Isct listset bvs2
        val _ = assert (HOLset.isEmpty bvfvs)
          (ERR "unify" "can't unify var with a tm containing bound vars")
      in
        elim sub (tm1, tm2) rest
      end
    else if is_var tm2 then solve' sub ((bvs2, tm2), (bvs1, tm1)) rest
    else
      (case Df dest_term (tm1, tm2) of
         (COMB (a1, b1), COMB (a2, b2)) =>
         let
           val s1 = ((bvs1, a1), (bvs2, a2))
           val s2 = ((bvs1, b1), (bvs2, b2))
         in
           solve' sub s1 (s2 :: rest)
         end
       | (LAMB (v1, b1), LAMB (v2, b2)) =>
         let
           val sub' = unify_reduce_ty (type_of v1) (type_of v2) sub
         in
           solve' sub' ((v1 :: bvs1, b1), (v2 :: bvs2, b2)) rest
         end
       | (CONST {Name, Thy, Ty}, CONST {Name = Name', Thy = Thy', Ty = Ty'}) =>
         let
           val _ =
             assert (Name = Name' andalso Thy = Thy')
             (ERR "unify" "different consts")
           val sub' = unify_reduce_ty Ty Ty' sub
         in
           solve sub' rest
         end
       | _ => raise ERR "unify" "terms fundamentally different")
  and elim sub (v, tm) rest =
    let
      val (tm_sub', ty_sub') = unify_reduce_ty (type_of v) (type_of tm) sub
      val (v', tm') = Df (inst_ty ty_sub') (v, tm)
    in
      if v' ~~ tm' then solve (tm_sub', ty_sub') rest
      else
        let
          val _ = assert (not (occurs v' tm')) (ERR "unify" "occurs check")
        in
          case total (tfind_redex v') tm_sub' of NONE =>
            let
              val sub' = refine_subst (tm_sub', ty_sub') ([v' |-> tm'], [])
            in
              solve sub' rest
            end
          | SOME {redex = _, residue}
            => solve' (tm_sub', ty_sub') (([], tm'), ([], residue)) rest
        end
    end
in
  fun unify_bvs (bvs1, tm1) (bvs2, tm2) =
    solve' empty_subst ((bvs1, tm1), (bvs2, tm2)) []
  fun unify tm1 tm2 = unify_bvs ([], tm1) ([], tm2)
end;

fun var_unify (tm_vars, ty_vars) tm1 tm2 =
  let
    val (tm_sub, ty_sub) = unify tm1 tm2
    val ty_renaming_sub = mk_renaming_subst_wrt_vars ty_vars ty_sub
    val (tm_sub', ty_sub') = refine_subst (tm_sub, ty_sub) ([], ty_renaming_sub)
    val tm_vars' = map (inst_ty ty_sub') tm_vars
    val tm_renaming_sub = mk_renaming_tsubst_wrt_vars tm_vars' tm_sub'
  in
    refine_subst (tm_sub', ty_sub') (tm_renaming_sub, [])
  end;

fun sep_var_unify (vars1, tm1) (vars2, tm2) =
  let
    (* Separate the variables *)
    val ((tm_gvars1, ty_gvars1), (old_to_new1, new_to_old1)) = new_vars vars1
    val ((tm_gvars2, ty_gvars2), (old_to_new2, new_to_old2)) = new_vars vars2
    (* Rename the variables in the terms to be unified *)
    val tm1' = pinst old_to_new1 tm1
    val tm2' = pinst old_to_new2 tm2
    (* Call unify *)
    val gvars = (tm_gvars1 @ tm_gvars2, ty_gvars1 @ ty_gvars2)
    val (tm_sub, ty_sub) = var_unify gvars tm1' tm2'
    (* Separate the returned substitution *)
    val (ty_sub1, ty_sub2) = partition (C mem ty_gvars1 o redex) ty_sub
    val tm_gvars1' = map (inst_ty ty_sub1) tm_gvars1
    val (tm_sub1, tm_sub2) = partition (C tmem tm_gvars1' o redex) tm_sub
    (* Rename back the variables in the separated substitutions *)
    val ty_renaming_sub = (snd new_to_old1 @ snd new_to_old2)
    val (ty_sub1', ty_sub2') =
      Df (clean_subst o (subst_map (D (type_inst ty_renaming_sub))))
      (ty_sub1, ty_sub2)
    val tm_renaming_sub1 =
      (clean_tsubst o subst_map (D (inst_ty ty_sub1'))) (fst new_to_old1)
    val tm_renaming_sub2 =
      (clean_tsubst o subst_map (D (inst_ty ty_sub2'))) (fst new_to_old2)
    val tm_renaming_sub = tm_renaming_sub1 @ tm_renaming_sub2
    val (tm_sub1', tm_sub2') =
      Df (clean_tsubst o subst_map (D (subst tm_renaming_sub)))
      (tm_sub1, tm_sub2)
  in
    ((tm_sub1', ty_sub1'), (tm_sub2', ty_sub2'))
  end;

fun sep_unify tm1 tm2 =
  let
    val vars1 = (free_vars tm1, type_vars_in_term tm1)
    val vars2 = (free_vars tm2, type_vars_in_term tm2)
  in
    sep_var_unify (vars1, tm1) (vars2, tm2)
  end;

(*
tt2 unify ``fred : bool`` ``T``;
tt2 unify ``[fred : 'bob; fred; barney]`` ``[T; wilma; wilma]``;
ff2 unify ``[fred; fred; F]`` ``[T; wilma; wilma]``;
tt2 unify ``!x. x`` ``!y. y``;
ff2 unify ``!x. fred x`` ``!y. wilma``;
ff2 unify ``!x. fred x`` ``!y z. wilma``;
tt2 unify ``!x. fred x`` ``!y. wilma y``;
tt2 unify ``!x:'a. P x`` ``!y:'a. P y``;
tt2 unify ``!x:'a. P x`` ``!y:'b. P y``;
ff2 unify ``fred ==> fred`` ``fred : bool``;
tt2 sep_unify ``fred ==> fred`` ``fred : bool``;
*)

(* non-interactive mode
*)
end;
