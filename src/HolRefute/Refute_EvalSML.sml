structure Refute_EvalSML = struct
  structure Names = Refute_ModelFinder_Names

  type term = Term.term

  exception Stuck of string
  (* A position is the constructor-field path from the quantified root.
     Narrowing catches this precise sentinel and re-runs from scratch after
     refining that position; unrelated exceptions must remain unrelated. *)
  exception Hole of int list
  exception Deadline

  datatype extraction_mode = StrictExtraction | LazyExtraction

  fun lazy_hole position = Susp.delay (fn () => raise Hole position)

  type reconstruction = unit -> term
  type generated_environment = (int * reconstruction) list
  type generated_hit =
    generated_environment * generated_environment option *
    Refute_Eval.case_tree option * bool
  type generated_answer =
    { hit : generated_hit option,
      complete : bool,
      table : int,
      state : IntInf.int,
      tests : int,
      match_failures : int,
      assumption_satisfied : int,
      conclusion_evaluated : int,
      candidates_generated : int }
  type generated_dispatch =
    int -> bool -> int -> int -> IntInf.int -> generated_answer

  val installed_dispatch : generated_dispatch option ref = ref NONE
  val deadline : Time.time option ref = ref NONE
  val ignored_filter : (generated_hit -> bool) ref = ref (fn _ => false)
  val constructors : term vector ref = ref (Vector.fromList [])
  val raw_terms : term vector ref = ref (Vector.fromList [])
  val table_serial = ref 0
  val term_tables = ref
    ([] : (int * term vector * term vector) list)
  val table_mutex = Mutex.mutex ()
  val native_mutex = Mutex.mutex ()
  val compiler_mutex = Mutex.mutex ()
  val goal_compile_mutex = Mutex.mutex ()
  val reconstruction_forces = ref 0

  (* Do not block with interrupts masked: [Timeout.apply] cancels by raising
     an interrupt.  The successful nonblocking acquisition occurs while
     masked, which still makes installing cleanup state atomic. *)
  fun lock_interruptibly restore lock =
    let
      fun acquire () =
        if Mutex.trylock lock then ()
        else
          (restore (fn () => OS.Process.sleep (Time.fromReal 0.01)) ();
           acquire ())
    in
      acquire ()
    end

  datatype install_result =
      Installed of generated_dispatch
    | CompileError of string list

  datatype extraction_result =
      Extracted of {source : string, entry : string, table : int}
    | ExtractionFailed of string list

  type extractor =
    extraction_mode -> Refute_Core.config -> Refute_Eval.strategy ->
    Refute_Eval.qc_problem -> extraction_result

  fun note_force () =
    reconstruction_forces := !reconstruction_forces + 1

  fun reset_reconstruction_forces () = reconstruction_forces := 0

  fun register_term_tables constructor_terms terms =
    Thread_Attributes.uninterruptible
      (fn restore => fn () =>
        let
          val _ = lock_interruptibly restore table_mutex
          val serial = !table_serial
          val entry =
            (serial, Vector.fromList constructor_terms,
             Vector.fromList terms)
          val _ = table_serial := serial + 1
          val _ = term_tables := entry :: !term_tables
          val _ = Mutex.unlock table_mutex
        in
          serial
        end) ()

  fun term_table_count () = length (!term_tables)

  fun unregister_term_tables serial =
    let
      fun remove () =
        term_tables := List.filter (fn (index, _, _) => index <> serial)
          (!term_tables)
    in
      Thread_Attributes.uninterruptible
        (fn restore => fn () =>
          (lock_interruptibly restore table_mutex;
           remove () before Mutex.unlock table_mutex)) ()
    end

  (* [restore] is fixed at unit by the interruptible lock acquisition, so
     the action's value leaves the masked region through a slot. *)
  fun with_term_tables serial action =
    Thread_Attributes.uninterruptible
      (fn restore => fn () =>
        let
          val _ = lock_interruptibly restore table_mutex
          val slot = ref NONE
          val result = Exn.capture (fn () =>
            let
              val (_, constructor_table, term_table) =
                valOf (List.find (fn (index, _, _) => index = serial)
                  (!term_tables))
              val old_constructors = !constructors
              val old_terms = !raw_terms
              val action_result = Exn.capture (restore (fn () =>
                (constructors := constructor_table;
                 raw_terms := term_table;
                 slot := SOME (action ())))) ()
              val _ = constructors := old_constructors
              val _ = raw_terms := old_terms
            in
              Exn.release action_result
            end) ()
          val _ = Mutex.unlock table_mutex
          val _ = Exn.release result
        in
          case !slot of
              SOME value => value
            | NONE => raise Fail
                "Refute_EvalSML.with_term_tables: no value"
        end) ()

  fun wrap_reconstruction serial rebuild () =
    with_term_tables serial rebuild

  fun check_deadline () =
    case !deadline of
        NONE => ()
      | SOME limit =>
          if Time.compare (Time.now (), limit) = LESS then ()
          else raise Deadline

  fun table_term serial index =
    with_term_tables serial (fn () => Vector.sub (!raw_terms, index))

  fun raw_term index =
    (note_force (); Vector.sub (!raw_terms, index))

  fun con_term index arguments =
    (note_force ();
     Term.list_mk_comb (Vector.sub (!constructors, index), arguments))

  fun num_term value =
    (note_force (); numSyntax.mk_numeral (Arbnum.fromLargeInt value))

  fun int_term value =
    (note_force (); intSyntax.term_of_int (Arbint.fromLargeInt value))

  fun char_term character =
    (note_force (); stringSyntax.fromMLchar character)

  fun string_term text =
    (note_force (); stringSyntax.fromMLstring text)

  fun is_char_list_type ty =
    Type.compare (ty, stringSyntax.string_ty) = EQUAL

  fun char_list_head_source value =
    "String.sub (" ^ value ^ ", 0)"

  fun char_list_tail_source value =
    "(if String.size (" ^ value ^ ") = 0 then \"\" else " ^
    "String.extract (" ^ value ^ ", 1, NONE))"

  fun char_list_value_parts value =
    let val text = Literal.relaxed_dest_string_lit value
    in
      if text = "" then NONE
      else SOME (String.sub (text, 0), String.extract (text, 1, NONE))
    end

  (* Narrowing holes use the M3 model-display marker constructor. *)
  fun hole_term type_index =
    (note_force ();
     Names.irrelevant_marker (Term.type_of (raw_term type_index)))

  fun replay_variable type_index position =
    let
      val suffix = String.concatWith "$" (map Int.toString position)
      val name = Names.reserved_prefix ^ "case$" ^ suffix
    in
      Term.mk_var (name, Term.type_of (raw_term type_index))
    end

  fun word_term width value =
    (note_force ();
     wordsSyntax.mk_wordi (Arbnum.fromLargeInt value, width))

  (* The abstraction is the constant function returning [default], so the
     binder is display only.  Vary it away from the free variables of the
     body: extraction cannot know them, and a name they already use would
     read as a capture. *)
  fun fun_term variable default updates =
    (note_force ();
     List.foldl (fn ((point, value), result) =>
       Term.mk_comb (combinSyntax.mk_update (point, value), result))
       (Term.mk_abs (Term.variant (Term.free_vars default) variable, default))
       updates)

  fun update_term point value base =
    (note_force ();
     Term.mk_comb (combinSyntax.mk_update (point, value), base))

  fun instantiate template environment =
    Term.subst (List.map (fn (index, thunk) =>
      {redex = raw_term index, residue = thunk ()}) environment) template

  fun eval_term index environment =
    let
      val application = instantiate (raw_term index) environment
      val theorem = computeLib.EVAL_CONV application
    in
      boolSyntax.rhs (Thm.concl theorem)
    end

  (* The reconstruction and split paths differ only in where the value comes
     from.  A char-list CONS reaches here as a string literal, which has to
     be taken apart textually rather than by [strip_comb]; a value that is
     not a literal falls back to the ordinary destructuring. *)
  fun constructor_argument constructor_index argument_index value =
    let
      val expected = Vector.sub (!constructors, constructor_index)
      val expected_name =
        let val {Thy, Name, ...} = Term.dest_thy_const expected
        in (Thy, Name) end
      val string_parts =
        if expected_name = ("list", "CONS") andalso
           is_char_list_type (Term.type_of value) then
          Lib.total char_list_value_parts value
        else NONE
    in
      case string_parts of
          SOME NONE => raise Stuck "empty string reconstruction"
        | SOME (SOME (head, tail)) =>
            if argument_index = 0 then char_term head
            else if argument_index = 1 then string_term tail
            else raise Subscript
        | NONE =>
            let val (constructor, arguments) = boolSyntax.strip_comb value
            in
              if Term.same_const constructor expected then
                List.nth (arguments, argument_index)
              else raise Stuck "constructor reconstruction mismatch"
            end
    end

  fun reconstruction_arg constructor_index argument_index rebuild () =
    constructor_argument constructor_index argument_index (rebuild ())

  fun split_term constructor_index argument_index expression_index
      environment =
    constructor_argument constructor_index argument_index
      (eval_term expression_index environment)

  fun pretty_string pretty =
    let
      val chunks = ref []
      val _ = PolyML.prettyPrint
        (fn chunk => chunks := chunk :: !chunks, 80) pretty
    in
      String.concat (rev (!chunks))
    end

  fun exception_text error =
    let val text = General.exnMessage error
    in if text = "" then "Poly/ML compiler failure" else text end

  fun compiler_errors source entry =
    let
      (* Rebinding this private compilation slot releases the previous
         namespace binding once its dispatch is no longer retained. *)
      val structure_name = "RefuteNative"
      val program =
        "structure " ^ structure_name ^ " = struct\n" ^ source ^
        "end\nval _ = " ^ structure_name ^ "." ^ entry ^ "\n"
      val stream = TextIO.openString program
      val chunks = ref []
      fun input () = TextIO.input1 stream
      fun error_message {context, hard, message, ...} =
        if not hard then ()
        else
          let
            val parts =
              (case context of NONE => [] | SOME pretty => [pretty]) @
              [message]
            val text = String.concat (List.map pretty_string parts)
          in
            (* Keep every hard-error chunk: Poly/ML may emit blank framing
               before the useful diagnostic. *)
            chunks := !chunks @ [text]
          end
      val parameters =
        [PolyML.Compiler.CPOutStream (fn _ => ()),
         PolyML.Compiler.CPErrorMessageProc error_message]
      fun loop () =
        if TextIO.endOfStream stream then ()
        else (PolyML.compiler (input, parameters) (); loop ())
      val result = Exn.capture loop ()
      val _ = TextIO.closeIn stream
    in
      case result of
          Exn.Res _ => if null (!chunks) then NONE else SOME (!chunks)
        | Exn.Exn Interrupt => raise Interrupt
        | Exn.Exn error =>
            SOME (if null (!chunks) then [exception_text error]
                  else !chunks)
    end

  (* Poly/ML enters generated structures in the global namespace.  Rebind
     one private slot instead of accumulating a fresh top-level name. *)
  fun compile_install source entry =
    Thread_Attributes.uninterruptible
      (fn restore => fn () =>
        let
          val _ = lock_interruptibly restore compiler_mutex
          val old_dispatch = !installed_dispatch
          val _ = installed_dispatch := NONE
          (* The lock acquisition above fixes [restore] at unit, so the
             compiler's diagnosis comes back through a slot. *)
          val slot = ref NONE
          val result = Exn.capture (restore (fn () =>
            slot := SOME (compiler_errors source entry))) ()
          val answer =
            case (result, !slot) of
                (Exn.Res _, SOME NONE) =>
                  (case !installed_dispatch of
                       SOME dispatch => Installed dispatch
                     | NONE => CompileError
                         ["generated code did not install its dispatch"])
              | (Exn.Res _, SOME (SOME errors)) => CompileError errors
              | (Exn.Res _, NONE) =>
                  CompileError ["compilation reported no diagnosis"]
              | (Exn.Exn Interrupt, _) =>
                  (installed_dispatch := old_dispatch;
                   Mutex.unlock compiler_mutex;
                   raise Interrupt)
              | (Exn.Exn error, _) => CompileError [exception_text error]
          val _ =
            (case answer of
                 Installed _ => ()
               | CompileError _ => installed_dispatch := old_dispatch)
          val _ = Mutex.unlock compiler_mutex
        in
          answer
        end) ()

  fun ignored_hit run_depth ignored
        (environment, grounding, case_tree, genuine) =
    let
      fun rebuild values = List.map (fn (index, reconstruction) =>
        (raw_term index, reconstruction ())) values
      val candidate =
        {env = rebuild environment,
         ground_env = Option.map rebuild grounding,
         case_tree = case_tree, genuine = genuine,
         run_depth = run_depth}
    in
      Refute_Eval.ignored_candidate candidate ignored
    end

  fun with_native_hooks limit run_depth ignored action =
    Thread_Attributes.uninterruptible
      (fn restore => fn () =>
        let
          val _ = lock_interruptibly restore native_mutex
          val old_deadline = !deadline
          val old_filter = !ignored_filter
          val _ = deadline := SOME limit
          val _ = ignored_filter := ignored_hit run_depth ignored
          (* One restore type per [uninterruptible] call: the action's answer
             travels through a slot, as in [with_term_tables]. *)
          val slot = ref NONE
          val result = Exn.capture
            (restore (fn () => slot := SOME (action ()))) ()
          val _ = deadline := old_deadline
          val _ = ignored_filter := old_filter
          val _ = Mutex.unlock native_mutex
          val _ = Exn.release result
        in
          case !slot of
              SOME value => value
            | NONE => raise Fail
                "Refute_EvalSML.with_native_hooks: no value"
        end) ()

  fun positive_time time = Time.compare (time, Time.zeroTime) = GREATER

  fun run_before limit action =
    let val remaining = Time.- (limit, Time.now ())
    in
      if positive_time remaining then Timeout.apply remaining action ()
      else raise Deadline
    end

  fun compile_locked extract (config : Refute_Core.config) strategy problem =
    let
      val search_context = Refute_Core.search_context_for config
      val started = #started search_context
      val limit = #deadline search_context
      val mode =
        case strategy of
            Refute_Eval.Narrowing => LazyExtraction
          | _ => StrictExtraction
      val extracted = extract mode config strategy problem
    in
      case extracted of
          ExtractionFailed reasons => Refute_Eval.Inapplicable reasons
        | Extracted {source, entry, table} =>
          (let
            val _ =
              if Refute_Core.Private.enabled 3 then
                Refute_Core.Private.say 3
                  ("Refute generated SML:\n" ^ source ^ "\n")
              else ()
          in
          case Exn.capture (fn () => compile_install source entry) () of
          Exn.Exn error =>
            (unregister_term_tables table; raise error)
        | Exn.Res (CompileError chunks) =>
            let
              val _ = unregister_term_tables table
              val detail = String.concat chunks
              val reason = "native: internal: " ^
                (if detail = "" then "generated code did not compile"
                 else detail)
              val _ = Refute_Core.Private.say 2 (reason ^ "\n")
            in
              Refute_Eval.Inapplicable [reason]
            end
        | Exn.Res (Installed dispatch) =>
            let
              val last_stats = ref []
              val state = ref
                (case strategy of
                     Refute_Eval.Exhaustive => 0
                   | Refute_Eval.Random {seed} => seed
                   | Refute_Eval.Narrowing => 0)
              val closed = ref false

              fun run input =
                let
                  fun invoke () = dispatch (#card input)
                    (#genuine_only input) (#size input) (#draws input)
                    (!state)
                  val run_depth =
                    case strategy of
                        Refute_Eval.Narrowing => SOME (#size input)
                      | _ => NONE
                  val answer = with_native_hooks limit run_depth
                    (#ignored input) (fn () => run_before limit invoke)
                  val _ = state := #state answer
                  val _ = last_stats :=
                    [("tests", #tests answer),
                     ("match_failures", #match_failures answer),
                     ("assumption_satisfied", #assumption_satisfied answer),
                     ("conclusion_evaluated", #conclusion_evaluated answer),
                     ("candidates_generated",
                       #candidates_generated answer)]
                in
                  case #hit answer of
                      NONE => Refute_Eval.Exhausted
                        {complete = #complete answer}
                    | SOME (environment, grounding, case_tree, genuine) =>
                        Refute_Eval.CexFound
                          {env = List.map (fn (index, rebuild) =>
                             (table_term (#table answer) index, rebuild ()))
                             environment,
                           ground_env = Option.map (List.map
                             (fn (index, rebuild) =>
                               (table_term (#table answer) index,
                                rebuild ()))) grounding,
                           case_tree = case_tree,
                           genuine = genuine,
                           run_depth = run_depth}
                end
                handle Deadline => Refute_Eval.GaveUp "deadline"
                     | Timeout.TIMEOUT _ => Refute_Eval.GaveUp "deadline"

              fun close () =
                if !closed then ()
                else (unregister_term_tables table; closed := true)
            in
              Refute_Eval.Compiled
                {run = run, close = close, max_chunk = NONE,
                 last_stats = last_stats}
            end
          end)
          handle error => (unregister_term_tables table; raise error)
    end
    handle Interrupt => raise Interrupt
         | error =>
             let
               val reason = "native: internal: " ^ exception_text error
               val _ = Refute_Core.Private.say 2 (reason ^ "\n")
             in
               Refute_Eval.Inapplicable [reason]
             end

  fun compile_problem extract config strategy problem =
    Thread_Attributes.uninterruptible
      (fn restore => fn () =>
        let
          val _ = lock_interruptibly restore goal_compile_mutex
          (* One restore type per [uninterruptible] call: the compilation
             result travels through a slot, as in [with_term_tables]. *)
          val slot = ref NONE
          val result = Exn.capture
            (restore (fn () =>
              slot := SOME
                (compile_locked extract config strategy problem))) ()
          val _ = Mutex.unlock goal_compile_mutex
          val _ = Exn.release result
        in
          case !slot of
              SOME value => value
            | NONE => raise Fail
                "Refute_EvalSML.compile_problem: no value"
        end) ()

  fun compile_with extract config strategy problem =
    compile_problem extract config strategy problem

  fun dump_native_random_candidates extract {plan, seed, size, count} =
    case compile_with extract Refute_Core.default_config
        (Refute_Eval.Random {seed = seed})
        (Refute_Eval.Plans [Refute_Eval.dump_plan plan]) of
        Refute_Eval.Inapplicable reasons =>
          raise Fail (String.concatWith "; " reasons)
      | Refute_Eval.Compiled test =>
          Refute_Eval.dump_stream test {size = size, count = count}

  fun native_substrate {preflight, extract} : Refute_Eval.substrate =
    {name = "native", priority = 10,
     accepts = fn _ => true,
     preflight = SOME preflight,
     compile = compile_with extract}

  fun register_substrate dependencies =
    Refute_Eval.register_substrate (native_substrate dependencies)
end
