structure Refute_ModelFinder_Names = struct
  type term = Term.term
  type hol_type = Type.hol_type

  val reserved_prefix = "refute$"
  val name_sep = "$"

  val numeral_prefix = reserved_prefix ^ "num" ^ name_sep
  val sel_prefix = reserved_prefix ^ "sel"
  val discr_prefix = reserved_prefix ^ "is" ^ name_sep
  val lfp_iterator_prefix = reserved_prefix ^ "lfpit" ^ name_sep
  val gfp_iterator_prefix = reserved_prefix ^ "gfpit" ^ name_sep
  val iterator_zero_prefix = reserved_prefix ^ "iterzero" ^ name_sep
  val iterator_suc_prefix = reserved_prefix ^ "itersuc" ^ name_sep
  val unrolled_prefix = reserved_prefix ^ "unroll" ^ name_sep
  val base_prefix = reserved_prefix ^ "base" ^ name_sep
  val step_prefix = reserved_prefix ^ "step" ^ name_sep
  val ubfp_prefix = reserved_prefix ^ "ubfp" ^ name_sep
  val lbfp_prefix = reserved_prefix ^ "lbfp" ^ name_sep
  val quot_normal_prefix = reserved_prefix ^ "qn" ^ name_sep
  val skolem_prefix = reserved_prefix ^ "sk"
  val special_prefix = reserved_prefix ^ "sp"
  val bound_var_prefix = reserved_prefix ^ "b"
  val cong_var_prefix = reserved_prefix ^ "c"
  val uncurry_prefix = reserved_prefix ^ "unc"
  val eval_prefix = reserved_prefix ^ "eval"
  val replay_hole_prefix = reserved_prefix ^ "replay_hole" ^ name_sep
  val iter_var_prefix = "i"
  val cyclic_co_val_name = "ω"
  val cyclic_co_val_name_ascii = "w"

  fun err function message =
    Feedback.mk_HOL_ERR "Refute_ModelFinder_Names" function message

  fun drop_prefix prefix string =
    String.extract (string, size prefix, NONE)

  fun eval_index name =
    if String.isPrefix eval_prefix name then
      let val suffix = drop_prefix eval_prefix name
      in
        case Int.fromString suffix of
            SOME index =>
              if index >= 0 andalso Int.toString index = suffix then SOME index
              else NONE
          | NONE => NONE
      end
    else NONE

  fun strip_first_name_sep string =
    let
      val (left, right) =
        Substring.position name_sep (Substring.full string)
      val suffix =
        if Substring.isEmpty right then right
        else Substring.triml (size name_sep) right
    in
      (Substring.string left, Substring.string suffix)
    end

  (* HOL4's reserved prefix itself ends in name_sep.  Strip that namespace
     first, then recurse through the remaining generated-name layer. *)
  fun original_name string =
    if String.isPrefix reserved_prefix string then
      let
        val body = drop_prefix reserved_prefix string
        val (_, original) = strip_first_name_sep body
      in
        if original = "" then string else original_name original
      end
    else
      string

  fun sel_prefix_for index =
    sel_prefix ^ Int.toString index ^ name_sep

  fun skolem_prefix_for arity serial =
    skolem_prefix ^ Int.toString arity ^ "@" ^ Int.toString serial ^
    name_sep

  fun special_prefix_for serial =
    special_prefix ^ Int.toString serial ^ name_sep

  fun bound_var_name index =
    bound_var_prefix ^ Int.toString index ^ name_sep

  fun cong_var_name index =
    cong_var_prefix ^ Int.toString index ^ name_sep

  fun is_sel name =
    String.isPrefix discr_prefix name orelse
    String.isPrefix sel_prefix name

  fun has_generated_layer prefix name =
    if String.isPrefix prefix name then
      true
    else
      let val (_, suffix) = strip_first_name_sep name
      in suffix <> "" andalso has_generated_layer prefix suffix end

  fun is_skolem_name name = has_generated_layer skolem_prefix name

  fun is_special_name name = String.isPrefix special_prefix name

  fun is_indexed_var_name prefix name =
    if not (String.isPrefix prefix name) then false
    else
      let
        val suffix = drop_prefix prefix name
        val length = size suffix
        val digits =
          if length < 1 then ""
          else String.extract (suffix, 0, SOME (length - 1))
      in
        length > 1 andalso String.isSuffix name_sep suffix andalso
        Lib.str_all Char.isDigit digits
      end

  fun is_bound_var_name name = is_indexed_var_name bound_var_prefix name

  fun is_cong_var_name name = is_indexed_var_name cong_var_prefix name

  fun sel_no_from_name name =
    if String.isPrefix discr_prefix name then
      ~1
    else if String.isPrefix sel_prefix name then
      let
        val suffix = drop_prefix sel_prefix name
        val (number, _) = strip_first_name_sep suffix
      in
        case Int.fromString number of
            SOME index => index
          | NONE => raise err "sel_no_from_name"
              ("malformed selector name: " ^ name)
      end
    else if name = "pair$SND" then
      1
    else
      0

  fun mk_reserved_var name ty =
    if String.isPrefix reserved_prefix name then
      Term.mk_var (name, ty)
    else
      raise err "mk_reserved_var" ("unreserved name: " ^ name)

  fun mk_numeral value ty =
    mk_reserved_var (numeral_prefix ^ Int.toString value) ty

  fun mk_discriminator constructor ty =
    mk_reserved_var (discr_prefix ^ constructor) ty

  fun mk_iterator_zero token ty =
    mk_reserved_var (iterator_zero_prefix ^ token) ty

  fun mk_iterator_suc token ty =
    mk_reserved_var (iterator_suc_prefix ^ token) (Type.-->(ty, ty))

  fun mk_unrolled original iterator_ty predicate_ty =
    mk_reserved_var (unrolled_prefix ^ original)
      (Type.-->(iterator_ty, predicate_ty))

  fun mk_base original predicate_ty =
    mk_reserved_var (base_prefix ^ original) predicate_ty

  fun mk_step original relation_ty =
    mk_reserved_var (step_prefix ^ original) relation_ty

  fun mk_ubfp original predicate_ty =
    mk_reserved_var (ubfp_prefix ^ original) predicate_ty

  fun mk_lbfp original predicate_ty =
    mk_reserved_var (lbfp_prefix ^ original) predicate_ty

  fun quot_normal_name_for_type ty =
    quot_normal_prefix ^ Parse.type_to_string ty

  fun mk_quot_normal abs_ty rep_ty =
    mk_reserved_var (quot_normal_name_for_type abs_ty)
      (Type.-->(rep_ty, rep_ty))

  fun is_quot_normal_name name =
    String.isPrefix quot_normal_prefix name

  fun is_iterator_zero_name name =
    String.isPrefix iterator_zero_prefix name

  fun is_iterator_suc_name name =
    String.isPrefix iterator_suc_prefix name

  fun is_unrolled_name name = has_generated_layer unrolled_prefix name
  fun is_base_name name = has_generated_layer base_prefix name
  fun is_step_name name = has_generated_layer step_prefix name
  fun is_ubfp_name name = has_generated_layer ubfp_prefix name
  fun is_lbfp_name name = has_generated_layer lbfp_prefix name

  fun mk_selector index constructor ty =
    if index < 0 then
      raise err "mk_selector" "negative selector index"
    else
      mk_reserved_var (sel_prefix_for index ^ constructor) ty

  fun mk_skolem arity serial original ty =
    if arity < 0 orelse serial < 0 then
      raise err "mk_skolem" "negative arity or serial"
    else
      mk_reserved_var (skolem_prefix_for arity serial ^ original) ty

  fun mk_special serial original ty =
    if serial < 1 then
      raise err "mk_special" "specialization serial must be positive"
    else
      mk_reserved_var (special_prefix_for serial ^ original) ty

  fun mk_bound_var index ty =
    if index < 0 then raise err "mk_bound_var" "negative bound index"
    else mk_reserved_var (bound_var_name index) ty

  fun mk_cong_var index ty =
    if index < 0 then raise err "mk_cong_var" "negative congruence index"
    else mk_reserved_var (cong_var_name index) ty

  fun mk_eval serial ty =
    if serial < 0 then
      raise err "mk_eval" "negative serial"
    else
      mk_reserved_var (eval_prefix ^ Int.toString serial) ty

  fun replay_hole_name serial =
    if serial < 0 then
      raise err "replay_hole_name" "negative serial"
    else
      replay_hole_prefix ^ Int.toString serial

  fun mk_replay_hole serial ty =
    mk_reserved_var (replay_hole_name serial) ty

  (* Namespace recognition is used only to prevent fabricated model atoms
     from colliding with present or future replay holes.  Logical hole
     authorization is deliberately sidecar-based, never prefix-based. *)
  fun is_replay_hole_name name = String.isPrefix replay_hole_prefix name

  fun is_replay_hole term =
    Term.is_var term andalso
    is_replay_hole_name (#1 (Term.dest_var term))

  fun unknown_marker ty = Term.mk_var ("?", ty)
  fun unrepresented_marker ty = Term.mk_var ("…", ty)
  fun unrepresented_marker_ascii ty = Term.mk_var ("...", ty)

  (* Display holes and irrelevant model fragments share this constructor.
     Recognition is kept beside construction so consumers never grow their
     own string-based interpretation of user variables. *)
  fun irrelevant_marker ty = Term.mk_var ("_", ty)

  fun is_irrelevant_marker term =
    Term.is_var term andalso
    Term.aconv term (irrelevant_marker (Term.type_of term))

  fun contains_irrelevant_marker term =
    List.exists is_irrelevant_marker (Term.free_vars_lr term)

  fun is_unknown_marker term =
    Term.is_var term andalso
    Term.aconv term (unknown_marker (Term.type_of term))

  fun is_unrepresented_marker term =
    Term.is_var term andalso
    Term.aconv term (unrepresented_marker_ascii (Term.type_of term))

  (* Every fixed-name display marker denotes an unspecified value, so no
     two occurrences -- even of the same marker -- are known to stand for
     the same thing.  A consumer that must not conflate distinct unknowns
     (e.g. an update-chain dedup) tests a whole subterm with this rather
     than a single predicate, since a marker can sit inside a compound
     point ([(T, ?)]) rather than be the point itself. *)
  fun is_display_marker term =
    is_unknown_marker term orelse is_irrelevant_marker term orelse
    is_unrepresented_marker term

  fun contains_display_marker term =
    List.exists is_display_marker (Term.free_vars_lr term)

  (* Reserve the marker identity before a backend inserts holes.  HOL free
     variables are identified by name and type, so colliding user variables
     must be varied at the shared front-end boundary. *)
  fun rename_irrelevant_collisions terms =
    let
      val frees =
        Refute_Util.distinct_terms (List.concat (map Term.free_vars_lr terms))
      fun rename (variable, (avoids, substitutions, renaming)) =
        if is_irrelevant_marker variable then
          let
            val fresh = Term.variant avoids variable
          in
            (fresh :: avoids,
             {redex = variable, residue = fresh} :: substitutions,
             (variable, fresh) :: renaming)
          end
        else
          (avoids, substitutions, renaming)
      val (_, substitutions, renaming) =
        List.foldl rename (frees, [], []) frees
    in
      (map (Term.subst (rev substitutions)) terms, rev renaming)
    end

  fun fake_atom serial ty =
    if serial < 1 then
      raise err "fake_atom" "atom serial must be positive"
    else
      Term.mk_var ("a" ^ Int.toString serial, ty)

  fun variable_name variable = #1 (Term.dest_var variable)

  fun is_reserved_name name = String.isPrefix reserved_prefix name

  fun reserved_frees term =
    List.filter (is_reserved_name o variable_name)
      (Term.free_vars_lr term)

  fun reserved_variables term =
    List.filter (is_reserved_name o variable_name) (Term.all_vars term)

  fun is_reserved_type_variable ty =
    Type.is_vartype ty andalso
    String.isPrefix ("'" ^ reserved_prefix) (Type.dest_vartype ty)

  fun reserved_type_variables term =
    List.filter is_reserved_type_variable (Term.type_vars_in_term term)

  fun assert_user_goal term =
    case reserved_variables term of
        variable :: _ =>
          raise err "assert_user_goal"
            ("reserved variable in user goal: " ^
             variable_name variable)
      | [] =>
          (case reserved_type_variables term of
               ty :: _ =>
                 raise err "assert_user_goal"
                   ("reserved type variable in user goal: " ^
                    Type.dest_vartype ty)
             | [] => ())

  fun theorem_terms theorem = Thm.concl theorem :: Thm.hyp theorem

  fun assert_no_reserved_in_theorem label theorem =
    case List.concat (map reserved_variables (theorem_terms theorem)) of
        [] => ()
      | variable :: _ =>
          raise err "assert_no_reserved_in_theorem"
            (label ^ ": reserved variable escaped: " ^
             variable_name variable)

  fun member_name name = List.exists (fn variable =>
    variable_name variable = name)

  (* Fabricated variables keep their stable names.  Any colliding user-goal
     free is renamed first, using HOL4's name-based variant discipline. *)
  fun rename_colliding_goal_vars fabricated goal =
    let
      val goal_frees = Term.free_vars_lr goal
      val goal_tyvars = Term.type_vars_in_term goal

      fun rename (variable, (avoids, substitutions, renaming)) =
        if member_name (variable_name variable) fabricated then
          let
            val (name, ty) = Term.dest_var variable
            val candidate =
              if is_reserved_name name then
                Term.mk_var ("user$" ^ name, ty)
              else
                variable
            val fresh = Term.variant avoids candidate
            val substitution = {redex = variable, residue = fresh}
          in
            (fresh :: avoids, substitution :: substitutions,
             (variable, fresh) :: renaming)
          end
        else
          (avoids, substitutions, renaming)

      fun fresh_tyvar avoids serial =
        let val ty = Type.mk_vartype ("'user" ^ Int.toString serial)
        in
          if List.exists (fn old => old = ty) avoids then
            fresh_tyvar avoids (serial + 1)
          else ty
        end

      fun rename_tyvar (ty, (serial, avoids, substitutions)) =
        if is_reserved_type_variable ty then
          let
            val fresh = fresh_tyvar avoids serial
          in
            (serial + 1, fresh :: avoids,
             {redex = ty, residue = fresh} :: substitutions)
          end
        else
          (serial, avoids, substitutions)

      val (_, substitutions, renaming) =
        List.foldl rename (fabricated @ goal_frees, [], []) goal_frees
      val (_, _, type_substitutions) =
        List.foldl rename_tyvar (0, goal_tyvars, []) goal_tyvars
      val type_substitutions = rev type_substitutions
      val renamed = Term.inst type_substitutions
        (Term.subst (rev substitutions) goal)
      val _ = assert_user_goal renamed
    in
      (renamed, rev renaming, type_substitutions)
    end
end
