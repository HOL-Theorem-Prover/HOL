Theory refuteCvClean
Ancestors
  refute_cv
Libs
  Refute

Datatype:
  clean_tree = CleanLeaf num | CleanNode clean_tree clean_tree
End

Inductive clean_enum:
  clean_enum 0 /\
  (!n. clean_enum n ==> clean_enum (SUC n))
End

val base_config =
  Refute.default_config
  |> Refute.upd_substrate Refute.Cv
  |> Refute.upd_backends (SOME ["exhaustive"])
  |> Refute.upd_sequential true
  |> Refute.upd_timeout 10.0

val clean_result = Refute.refute
  (Refute.upd_size 3 base_config)
  ``(tree : clean_tree) = CleanLeaf 0``

val _ =
  case clean_result of
      Refute.Counterexample
        ({substrate = "cv", cert = SOME _, ...} :: _) => ()
    | _ => raise Fail "cv did not certify the export-cleanliness goal"

val enum_config = base_config
  |> Refute.upd_size 1
  |> Refute.upd_depth 4
  |> Refute.upd_certify false

val enum_goal = ``clean_enum (n : num) ==> n < 3``
val enum_plan = Refute_QC.compile_plan enum_config enum_goal

fun has_enum plan =
  case plan of
      Refute_Eval.Enum _ => true
    | Refute_Eval.Gen (_, next) => has_enum next
    | Refute_Eval.Bind (_, _, fallback, next) =>
        has_enum next orelse Option.getOpt (Option.map has_enum fallback, false)
    | Refute_Eval.Split (_, branches) =>
        List.exists (has_enum o #3) branches
    | Refute_Eval.Guard (_, next) => has_enum next
    | Refute_Eval.SmartGuard {cont, ...} => has_enum cont
    | _ => false

val _ = if has_enum enum_plan then ()
  else raise Fail "cv cleanliness goal did not contain Enum"

val enum_result = Refute.refute enum_config enum_goal

val _ =
  case enum_result of
      Refute.Counterexample
        ({substrate = "cv", certainty = Refute.Genuine,
          cert = NONE, ...} :: _) => ()
    | _ => raise Fail "cv did not execute the Enum cleanliness goal"
