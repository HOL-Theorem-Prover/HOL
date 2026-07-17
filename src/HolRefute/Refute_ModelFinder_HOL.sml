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
  val unrolled_prefix = reserved_prefix ^ "unroll" ^ name_sep
  val base_prefix = reserved_prefix ^ "base" ^ name_sep
  val step_prefix = reserved_prefix ^ "step" ^ name_sep
  val ubfp_prefix = reserved_prefix ^ "ubfp" ^ name_sep
  val lbfp_prefix = reserved_prefix ^ "lbfp" ^ name_sep
  val quot_normal_prefix = reserved_prefix ^ "qn" ^ name_sep
  val skolem_prefix = reserved_prefix ^ "sk"
  val special_prefix = reserved_prefix ^ "sp"
  val uncurry_prefix = reserved_prefix ^ "unc"
  val eval_prefix = reserved_prefix ^ "eval"
  val iter_var_prefix = "i"

  fun err function message =
    Feedback.mk_HOL_ERR "Refute_ModelFinder_Names" function message

  fun drop_prefix prefix string =
    String.extract (string, size prefix, NONE)

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

  fun mk_eval serial ty =
    if serial < 0 then
      raise err "mk_eval" "negative serial"
    else
      mk_reserved_var (eval_prefix ^ Int.toString serial) ty

  fun unknown_marker ty = Term.mk_var ("?", ty)
  fun unrepresented_marker ty = Term.mk_var ("…", ty)
  fun unrepresented_marker_ascii ty = Term.mk_var ("...", ty)
  fun irrelevant_marker ty = Term.mk_var ("_", ty)

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

  fun assert_user_goal term =
    case reserved_variables term of
        [] => ()
      | variable :: _ =>
          raise err "assert_user_goal"
            ("reserved variable in user goal: " ^
             variable_name variable)

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
      val _ = assert_user_goal goal
      val goal_frees = Term.free_vars_lr goal

      fun rename (variable, (avoids, substitutions, renaming)) =
        if member_name (variable_name variable) fabricated then
          let
            val fresh = Term.variant avoids variable
            val substitution = {redex = variable, residue = fresh}
          in
            (fresh :: avoids, substitution :: substitutions,
             (variable, fresh) :: renaming)
          end
        else
          (avoids, substitutions, renaming)

      val (_, substitutions, renaming) =
        List.foldl rename (fabricated @ goal_frees, [], []) goal_frees
    in
      (Term.subst (rev substitutions) goal, rev renaming)
    end
end
