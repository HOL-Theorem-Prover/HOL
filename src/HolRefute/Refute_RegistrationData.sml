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

  val ERR = Feedback.mk_HOL_ERR "Refute_RegistrationData"
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
  fun fresh d = uptodate (encode d) andalso
    (let val {Thy, Tyop} = operator d
     in Option.isSome (Type.op_arity {Thy = Thy, Tyop = Tyop}) end)

  (* Broken batches remain visible: hook warnings must not turn corrupt
     metadata into an absent entry that harvesting could rescue. *)
  datatype batch = Batch of string * descriptor list * t
                 | Broken of string * string * t
  fun batch_sexp (Batch (_, _, s)) = s
    | batch_sexp (Broken (_, _, s)) = s
  fun batch_origin (Batch (thy, _, _)) = thy
    | batch_origin (Broken (thy, _, _)) = thy
  fun decode_batch s =
    let
      val origin = case s of
          List [Int _, String thy, Int _, _] => thy
        | _ => "<unknown theory>"
    in
      SOME (case s of
          List [Int 1, String thy, Int _, ds] =>
            (case list_decode decode ds of
                 SOME entries =>
                   ((List.app (fn d => ignore (operator d)) entries;
                     Batch (thy, entries, s))
                    handle Feedback.HOL_ERR error => Broken
                      (thy, "malformed operator: " ^
                            Feedback.message_of error, s))
               | NONE => Broken (thy, "malformed descriptor", s))
        | List [Int version, _, _, _] => Broken (origin,
            "unsupported format version " ^ Int.toString version, s)
        | _ => Broken (origin, "malformed batch", s))
    end
  type value =
    {seen : t list,
     histories : (string * descriptor) list KNametab.table,
     operators : operator list,
     errors : (string * string) list}
  val empty : value =
    {seen = [], histories = KNametab.empty, operators = [], errors = []}
  fun key ({Thy, Tyop} : operator) = {Thy = Thy, Name = Tyop}
  fun apply batch (value : value) =
    if List.exists (fn old => compare (old, batch_sexp batch) = EQUAL)
         (#seen value) then value
    else
      let
        fun add thy (d, (histories, operators)) =
          let
            val opn = operator d
            val history = case KNametab.lookup histories (key opn) of
                NONE => [] | SOME ds => ds
          in
            (KNametab.update (key opn, history @ [(thy, d)]) histories,
             if List.exists (fn old => old = opn) operators then operators
             else operators @ [opn])
          end
        val (histories, operators, errors) = case batch of
            Broken (thy, why, _) =>
              (#histories value, #operators value,
               #errors value @ [(thy, why)])
          | Batch (thy, ds, _) =>
              let val (hs, ops) = List.foldl (add thy)
                    (#histories value, #operators value) ds
              in (hs, ops, #errors value) end
      in
        {seen = #seen value @ [batch_sexp batch], histories = histories,
         operators = operators, errors = errors}
      end

  val store = AncestryData.fullmake
    {adinfo = {tag = "Refute.structural_registrations",
               initial_values = [("min", empty)], apply_delta = apply},
     (* Replay and theory export check retirement against the retained
        history, even if the raw ancestry deltas have been pruned. *)
     uptodate_delta = fn _ => true,
     sexps = {enc = batch_sexp, dec = decode_batch},
     globinfo = {initial_value = empty, apply_to_global = apply,
                 thy_finaliser = NONE}}
  (* Delta side effects alone follow module loading order, which differs
     from ancestry merge order for siblings (and for late initialization).
     After fullmake's load hooks have built the per-theory values, publish
     the canonical merge.  Preserve deltas authored in the current theory.
     Listener runs older hooks first; this hook is registered afterwards.
     All work here is structural bookkeeping, never Refute validation. *)
  fun synchronise () =
    case #merge store (Theory.parents "-") of
        NONE => ()
      | SOME inherited =>
          let
            val local_deltas = case Context.current_thy (Context.snapshot ()) of
                NONE => []
              | SOME thy =>
                  let
                    (* Raw deltas may already have been pruned after a
                       retirement.  Keep authored history across imports
                       so the export check can still diagnose that loss. *)
                    val retained = List.filter
                      (fn d => batch_origin d = thy)
                      (List.mapPartial decode_batch
                        (#seen (#get_global_value store ())))
                  in retained @ #get_deltas store {thyname = thy} end
            val value = List.foldl (fn (d, v) => apply d v)
              inherited local_deltas
          in #update_global_value store (fn _ => value) end
  val _ = Theory.register_hook
    ("Refute_RegistrationData.ancestry_merge", fn delta =>
      case delta of TheoryDelta.TheoryLoaded _ => synchronise () | _ => ())
  val _ = synchronise ()

  (* AncestryData prunes a whole raw batch when any of its terms retires,
     before consulting uptodate_delta.  The global history retains every
     descriptor: check it before writing a theory so pruning cannot silently
     erase valid entries from the same batch in a subsequent process. *)
  fun check_export thy =
    let
      val value = #get_global_value store ()
      fun check opn =
        List.app (fn (origin, d) =>
          if fresh d then () else raise ERR "export"
            ("exporting theory " ^ thy ^ ", registration from " ^ origin ^
             ", " ^ #Thy opn ^ "$" ^ #Tyop opn ^
             ": registration refers to retired symbols"))
          (valOf (KNametab.lookup (#histories value) (key opn)))
    in List.app check (#operators value) end
  val _ = Theory.register_hook
    ("Refute_RegistrationData.check_export", fn delta =>
      case delta of TheoryDelta.ExportTheory thy => check_export thy
                  | _ => ())

  fun read ctxt =
    let val value = #get_global_value_of store ctxt
    in
      case #errors value of
          [] => value
        | (thy, why) :: _ => raise ERR "import"
            ("exporting theory " ^ thy ^ ": " ^ why)
    end
  fun history ctxt opn =
    case KNametab.lookup (#histories (read ctxt)) (key opn) of
        NONE => [] | SOME ds => ds
  fun operators ctxt = #operators (read ctxt)
  val identity = mk_list (pair_encode (String, encode))
  fun prepare ctxt thy descriptors =
    let
      val index = length (#get_deltas store {thyname = thy})
      val sexp = List [Int 1, String thy, Int index,
                       mk_list encode descriptors]
      val batch = Batch (thy, descriptors, sexp)
      val value = apply batch (#get_global_value_of store ctxt)
    in
      fn () => (#record_delta store batch;
                #update_global_value store (fn _ => value))
    end
end
