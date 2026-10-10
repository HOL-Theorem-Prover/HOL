structure Refute_RegistrationData :> Refute_RegistrationData = struct
  open ThyDataSexp
  type operator = {Thy : string, Tyop : string}
  datatype descriptor =
      Codata of {tyop : operator, case_const : Term.term,
                 constructors : Term.term list, witness : Thm.thm option}
    | Typedef of {ty : Type.hol_type, abs : Term.term, rep : Term.term,
                  absrep_thms : Thm.thm list}
    | Quotient of {qty : Type.hol_type, rty : Type.hol_type,
                   abs : Term.term, rep : Term.term, equiv_thm : Thm.thm}

  exception Invalid of Feedback.hol_error
  fun type_operator ty =
    let val {Thy, Tyop, ...} = Type.dest_thy_type ty
    in {Thy = Thy, Tyop = Tyop} end
  fun operator (Codata {tyop, ...}) = tyop
    | operator (Typedef {ty, ...}) = type_operator ty
    | operator (Quotient {qty, ...}) = type_operator qty

  val operator_ed = bij_ed
    ((fn {Thy, Tyop} => (Thy, Tyop)),
     (fn (thy, tyop) => {Thy = thy, Tyop = tyop}))
    (pair_ed (string_ed, string_ed))
  val codata_ed = bij_ed
    ((fn {tyop, case_const, constructors, witness} =>
        (tyop, case_const, constructors, witness)),
     (fn (tyop, case_const, constructors, witness) =>
        {tyop = tyop, case_const = case_const,
         constructors = constructors, witness = witness}))
    (pair4_ed (operator_ed, term_ed, list_ed term_ed, option_ed thm_ed))
  val typedef_ed = bij_ed
    ((fn {ty, abs, rep, absrep_thms} => (ty, abs, rep, absrep_thms)),
     (fn (ty, abs, rep, absrep_thms) =>
        {ty = ty, abs = abs, rep = rep, absrep_thms = absrep_thms}))
    (pair4_ed (type_ed, term_ed, term_ed, list_ed thm_ed))
  val quotient_ed = bij_ed
    ((fn {qty, rty, abs, rep, equiv_thm} =>
        (qty, rty, abs, (rep, equiv_thm))),
     (fn (qty, rty, abs, (rep, equiv_thm)) =>
        {qty = qty, rty = rty, abs = abs, rep = rep,
         equiv_thm = equiv_thm}))
    (pair4_ed (type_ed, type_ed, term_ed, pair_ed (term_ed, thm_ed)))
  val (encode, decode) = bij_ed
    ((fn Codata d => in13 d | Typedef d => in23 d | Quotient d => in33 d),
     (fn in13 d => Codata d | in23 d => Typedef d | in33 d => Quotient d))
    (tagged_sum3 ("codata", codata_ed) ("typedef", typedef_ed)
                 ("quotient", quotient_ed))
  fun fresh d =
    (case d of
         Codata {case_const, constructors, witness, ...} =>
           Term.uptodate_term case_const andalso
           List.all Term.uptodate_term constructors andalso
           (case witness of NONE => true | SOME th => Theory.uptodate_thm th)
       | Typedef {ty, abs, rep, absrep_thms} =>
           Type.uptodate_type ty andalso Term.uptodate_term abs andalso
           Term.uptodate_term rep andalso
           List.all Theory.uptodate_thm absrep_thms
       | Quotient {qty, rty, abs, rep, equiv_thm} =>
           Type.uptodate_type qty andalso Type.uptodate_type rty andalso
           Term.uptodate_term abs andalso Term.uptodate_term rep andalso
           Theory.uptodate_thm equiv_thm) andalso
    (let val {Thy, Tyop} = operator d
     in Option.isSome (Type.op_arity {Thy = Thy, Tyop = Tyop}) end)

  (* Broken deltas remain visible so harvesting cannot rescue corrupt data. *)
  datatype delta = Entry of string * descriptor * t
                 | Broken of string * string * t
  fun encode_delta (Entry (_, _, raw)) = raw
    | encode_delta (Broken (_, _, raw)) = raw
  fun decode_delta s = SOME (case s of
      List [Int 1, String thy, ds] =>
        (case decode ds of
             SOME d =>
               ((ignore (operator d); Entry (thy, d, s))
                handle Feedback.HOL_ERR error => Broken
                  (thy, "malformed operator: " ^ Feedback.message_of error, s))
           | NONE => Broken (thy, "malformed descriptor", s))
    | List (Int version :: String thy :: _) =>
        if version <> 1 then Broken (thy,
          "unsupported format version " ^ Int.toString version, s)
        else Broken ("<unknown theory>", "malformed delta", s)
    | _ => Broken ("<unknown theory>", "malformed delta", s))
  type value =
    {histories : (string * descriptor) list KNametab.table,
     operators : operator list,
     errors : (string * string) list}
  val empty : value =
    {histories = KNametab.empty, operators = [], errors = []}
  fun key ({Thy, Tyop} : operator) = {Thy = Thy, Name = Tyop}
  fun apply delta (value : value) =
    case delta of
        Broken (thy, why, _) =>
          {histories = #histories value, operators = #operators value,
           errors = #errors value @ [(thy, why)]}
      | Entry (thy, d, _) =>
          let
            val opn = operator d
            val old = KNametab.lookup (#histories value) (key opn)
          in
            {histories = KNametab.update
               (key opn, Option.getOpt (old, []) @ [(thy, d)])
               (#histories value),
             operators = if Option.isSome old then #operators value
                         else #operators value @ [opn],
             errors = #errors value}
          end

  val store = AncestryData.fullmake
    {adinfo = {tag = "Refute.structural_registrations",
               initial_values = [("min", empty)], apply_delta = apply},
     (* Raw-sexp pruning already checks freshness; this states intent. *)
     uptodate_delta = fn Entry (_, d, _) => fresh d | Broken _ => true,
     sexps = {enc = encode_delta, dec = decode_delta},
     globinfo = {initial_value = empty, apply_to_global = apply,
                 thy_finaliser = NONE}}
  (* Load-time side effects follow module loading order, which differs
     from ancestry merge order for siblings and late initialization, so
     republish the canonical merge plus the current theory's own deltas.
     Registered after fullmake's hooks, so it runs after them.  Structural
     bookkeeping only, never Refute validation. *)
  fun synchronise () =
    case #merge store (Theory.parents "-") of
        NONE => ()
      | SOME inherited =>
          let
            val local_deltas =
              case Context.current_thy (Context.snapshot ()) of
                  NONE => []
                | SOME thy => #get_deltas store {thyname = thy}
            val value = List.foldl (fn (d, v) => apply d v)
              inherited local_deltas
          in #update_global_value store (fn _ => value) end
  val _ = Theory.register_hook
    ("Refute_RegistrationData.ancestry_merge", fn delta =>
      case delta of TheoryDelta.TheoryLoaded _ => synchronise () | _ => ())
  val _ = synchronise ()

  fun read ctxt =
    let val value = #get_global_value_of store ctxt
    in
      case #errors value of
          [] => value
        | (thy, why) :: _ => raise Invalid (Feedback.mk_hol_error
            "Refute_RegistrationData" "import" locn.Loc_None
            ("exporting theory " ^ thy ^ ": " ^ why))
    end
  fun history ctxt opn =
    case KNametab.lookup (#histories (read ctxt)) (key opn) of
        NONE => [] | SOME ds => List.filter (fresh o #2) ds
  fun operators ctxt =
    List.filter (fn opn => not (null (history ctxt opn)))
      (#operators (read ctxt))
  val identity = mk_list (pair_encode (String, encode))
  fun prepare ctxt thy descriptors =
    let
      val entries = map (fn d => Entry
        (thy, d, List [Int 1, String thy, encode d])) descriptors
      val value = List.foldl (fn (d, v) => apply d v)
        (#get_global_value_of store ctxt) entries
    in
      fn () => (List.app (#record_delta store) entries;
                #update_global_value store (fn _ => value))
    end
end
