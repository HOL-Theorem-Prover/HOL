structure hhStature :> hhStature =
struct

open HolKernel boolSyntax aiLib

type stature =
  {simp : bool, local_ : bool, def : bool, induction : bool}
type induction_concls = (goal, unit) Redblackmap.dict
type statures = (string, stature) Redblackmap.dict

val empty_stature =
  {simp = false, local_ = false, def = false, induction = false}

fun thmid_of_kname ({Thy, Name} : KernelSig.kernelname) =
  Thy ^ "Theory." ^ Name

fun theory_name_of thmid =
  case total (split_string "Theory.") thmid of
      SOME (thy, name) =>
        if thy <> "" andalso name <> "" andalso
           thy <> mlThmData.namespace_tag
        then SOME (thy, name)
        else NONE
    | NONE => NONE

fun remove_thmid thmid names =
  #1 (Redblackmap.remove (names, thmid)) handle Redblackmap.NotFound => names

fun remove_from_set removed names =
  case String.fields (fn c => c = #".") removed of
      [name] =>
        dfoldl
          (fn (thmid, (), result) =>
            case theory_name_of thmid of
                SOME (_, thmname) =>
                  if thmname = name then remove_thmid thmid result
                  else result
              | NONE => result)
          names names
    | [thy, name] => remove_thmid (thy ^ "Theory." ^ name) names
    | _ => remove_thmid removed names

fun simp_set_of_deltas deltas =
  foldl
    (fn (delta, names) =>
      case delta of
          ThmSetData.ADD (kname, _) =>
            dadd (thmid_of_kname kname) () names
        | ThmSetData.REMOVE name => remove_from_set name names)
    (dempty String.compare) deltas

val simp_thmids_of_deltas = dkeys o simp_set_of_deltas

fun simp_deltas_of_theories theories =
  List.concat (map (fn thy =>
    ThmSetData.theory_data {settype = "simp", thy = thy}) theories)

fun target_theories target =
  mk_sameorder_set String.compare (Theory.ancestry target @ [target])

fun induction_concls_of thms =
  foldl
    (fn (thm, conclusions) =>
      dadd ([], Thm.concl thm) () conclusions)
    (dempty goal_compare) thms

fun induction_by_concl conclusions conclusion =
  dmem ([], conclusion) conclusions

fun predicate_type ty =
  let val (arguments, result) = strip_fun ty in
    not (null arguments) andalso result = Type.bool
  end

fun lower_string string = CharVector.map Char.toLower string

fun base_name thmid =
  case theory_name_of thmid of
      SOME (_, name) => name
    | NONE => thmid

fun induction_by_shape thmid conclusion =
  String.isSubstring "induct" (lower_string (base_name thmid)) andalso
  List.exists (predicate_type o type_of) (#1 (strip_forall conclusion))

fun typebase_induction_concls theories =
  case TypeBase.merge_typebases theories of
      NONE => induction_concls_of []
    | SOME typebase =>
        TypeBasePure.listItems typebase
        |> List.mapPartial (total TypeBasePure.induction_of)
        |> induction_concls_of

fun definition_set theories =
  let
    fun add_presentation (presentation, definitions) =
      dadd (thmid_of_kname (#thmname presentation)) () definitions
  in
    foldl add_presentation (dempty String.compare)
      (List.concat (map (fn theory =>
         DefnBaseCore.thy_userdefs {thyname = theory}) theories))
  end

fun add_db_stature current simp_names def_names induction_conclusions
      ((((thy, name), (thm, info))) : DB.data, result) =
  let
    val thmid = thy ^ "Theory." ^ name
    val def = dmem thmid def_names orelse #class info = DB.Def
    val induction =
      induction_by_concl induction_conclusions (Thm.concl thm) orelse
      induction_by_shape thmid (Thm.concl thm)
    val stature =
      {simp = dmem thmid simp_names, local_ = thy = current,
       def = def, induction = induction}
  in
    dadd thmid stature result
  end

fun create_statures_for current =
  let
    val theories = target_theories current
    val simp_names =
      simp_set_of_deltas (simp_deltas_of_theories theories)
    val def_names = definition_set theories
    val induction_conclusions = typebase_induction_concls theories
    val database = List.concat (map DB.thy theories)
  in
    foldl (add_db_stature current simp_names def_names
      induction_conclusions) (dempty String.compare) database
  end

fun create_statures () = create_statures_for (Theory.current_theory ())

fun stature_of statures thmid =
  case Redblackmap.peek (statures, thmid) of
      NONE => empty_stature
    | SOME stature =>
        if Option.isSome (theory_name_of thmid) then stature
        else empty_stature

end
