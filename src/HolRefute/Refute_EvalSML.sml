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
      match_failures : int }
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
  val compile_serial = ref 0
  val reconstruction_forces = ref 0

  datatype install_result =
      Installed of generated_dispatch
    | CompileError of string list

  datatype extraction_result =
      Extracted of {source : string, entry : string, table : int}
    | ExtractionFailed of string list

  val extract_tests_hook = ref
    (fn (_ : extraction_mode) =>
      fn (_ : Refute_Core.config) =>
      fn (_ : Refute_Eval.strategy) =>
      fn (_ : Refute_Eval.qc_problem) =>
        ExtractionFailed ["native: extractor is not installed"])

  fun note_force () =
    reconstruction_forces := !reconstruction_forces + 1

  fun reset_reconstruction_forces () = reconstruction_forces := 0

  fun install_constructors terms =
    constructors := Vector.fromList terms

  fun install_raw_terms terms =
    raw_terms := Vector.fromList terms

  fun register_term_tables constructor_terms terms =
    Thread_Attributes.uninterruptible
      (fn _ => fn () =>
        let
          val _ = Mutex.lock table_mutex
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
        (fn _ => fn () =>
          (Mutex.lock table_mutex;
           remove () before Mutex.unlock table_mutex)) ()
    end

  fun with_term_tables serial action =
    Thread_Attributes.uninterruptible
      (fn restore => fn () =>
        let
          val _ = Mutex.lock table_mutex
          val (_, constructor_table, term_table) =
            valOf (List.find (fn (index, _, _) => index = serial)
              (!term_tables))
          val old_constructors = !constructors
          val old_terms = !raw_terms
          val result = Exn.capture (restore (fn () =>
            (constructors := constructor_table;
             raw_terms := term_table;
             action ()))) ()
          val _ = constructors := old_constructors
          val _ = raw_terms := old_terms
          val _ = Mutex.unlock table_mutex
        in
          Exn.release result
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

  fun fun_term variable default updates =
    (note_force ();
     List.foldl (fn ((point, value), result) =>
       Term.mk_comb (combinSyntax.mk_update (point, value), result))
       (Term.mk_abs (variable, default)) updates)

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

  fun reconstruction_arg constructor_index argument_index rebuild () =
    let
      val value = rebuild ()
      val expected = Vector.sub (!constructors, constructor_index)
      val expected_name =
        let val {Thy, Name, ...} = Term.dest_thy_const expected
        in (Thy, Name) end
      val string_cons = expected_name = ("list", "CONS") andalso
        Type.compare (Term.type_of value, stringSyntax.string_ty) = EQUAL
    in
      if string_cons then
        let val text = Literal.relaxed_dest_string_lit value
        in
          if text = "" then raise Stuck "empty string reconstruction"
          else if argument_index = 0 then char_term (String.sub (text, 0))
          else if argument_index = 1 then
            string_term (String.extract (text, 1, NONE))
          else raise Subscript
        end
      else
        let val (constructor, arguments) = boolSyntax.strip_comb value
        in
          if Term.same_const constructor expected then
            List.nth (arguments, argument_index)
          else raise Stuck "constructor reconstruction mismatch"
        end
    end

  fun split_term constructor_index argument_index expression_index
      environment =
    let
      val value = eval_term expression_index environment
      val expected = Vector.sub (!constructors, constructor_index)
      val expected_name =
        let val {Thy, Name, ...} = Term.dest_thy_const expected
        in (Thy, Name) end
      val expected_result =
        #2 (boolSyntax.strip_fun (Term.type_of expected))
      val string_cons = expected_name = ("list", "CONS") andalso
        Type.compare (expected_result, stringSyntax.string_ty) = EQUAL
      fun ordinary () =
        let val (constructor, arguments) = boolSyntax.strip_comb value
        in
          if Term.same_const constructor expected then
            List.nth (arguments, argument_index)
          else
            raise Stuck "constructor reconstruction mismatch"
        end
      fun string_argument () =
        let val text = Literal.relaxed_dest_string_lit value
        in
          if expected_name = ("list", "CONS") andalso text <> "" then
            if argument_index = 0 then char_term (String.sub (text, 0))
            else if argument_index = 1 then
              string_term (String.extract (text, 1, NONE))
            else raise Subscript
          else
            raise Stuck "string reconstruction mismatch"
        end
    in
      if string_cons then string_argument () else ordinary ()
    end

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
      val serial = !compile_serial
      val _ = compile_serial := serial + 1
      val structure_name = "RefuteNative_" ^ Int.toString serial
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

  (* Poly/ML enters each generated structure in the global namespace.
     Gensymming makes one compile safe, but the shadowed structures retain
     a bounded amount of memory per goal-set; process isolation is the only
     in-tree way to reclaim those bindings. *)
  fun compile_install source entry =
    Thread_Attributes.uninterruptible
      (fn restore => fn () =>
        let
          val _ = Mutex.lock compiler_mutex
          val old_dispatch = !installed_dispatch
          val _ = installed_dispatch := NONE
          val result = Exn.capture (restore (fn () =>
            compiler_errors source entry)) ()
          val answer =
            case result of
                Exn.Res NONE =>
                  (case !installed_dispatch of
                       SOME dispatch => Installed dispatch
                     | NONE => CompileError
                         ["generated code did not install its dispatch"])
              | Exn.Res (SOME errors) => CompileError errors
              | Exn.Exn Interrupt =>
                  (installed_dispatch := old_dispatch;
                   Mutex.unlock compiler_mutex;
                   raise Interrupt)
              | Exn.Exn error => CompileError [exception_text error]
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
          val _ = Mutex.lock native_mutex
          val old_deadline = !deadline
          val old_filter = !ignored_filter
          val _ = deadline := SOME limit
          val _ = ignored_filter := ignored_hit run_depth ignored
          val result = Exn.capture (restore action) ()
          val _ = deadline := old_deadline
          val _ = ignored_filter := old_filter
          val _ = Mutex.unlock native_mutex
        in
          Exn.release result
        end) ()

  fun positive_time time = Time.compare (time, Time.zeroTime) = GREATER

  fun run_before limit action =
    let val remaining = Time.- (limit, Time.now ())
    in
      if positive_time remaining then Timeout.apply remaining action ()
      else raise Deadline
    end

  fun compile_locked (config : Refute_Core.config) strategy problem =
    let
      val started = Time.now ()
      val timeout = Time.fromReal (Real.max (0.0, #timeout config))
      val limit = Time.+ (started, timeout)
      val mode =
        case strategy of
            Refute_Eval.Narrowing => LazyExtraction
          | _ => StrictExtraction
      val extracted = (!extract_tests_hook) mode config strategy problem
    in
      case extracted of
          ExtractionFailed reasons => Refute_Eval.Inapplicable reasons
        | Extracted {source, entry, table} =>
          let
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
                     ("match_failures", #match_failures answer)]
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
          end
    end
    handle Interrupt => raise Interrupt
         | error =>
             let
               val reason = "native: internal: " ^ exception_text error
               val _ = Refute_Core.Private.say 2 (reason ^ "\n")
             in
               Refute_Eval.Inapplicable [reason]
             end

  fun compile_problem config strategy problem =
    Thread_Attributes.uninterruptible
      (fn restore => fn () =>
        let
          val _ = Mutex.lock goal_compile_mutex
          val result = Exn.capture
            (restore (fn () => compile_locked config strategy problem)) ()
          val _ = Mutex.unlock goal_compile_mutex
        in
          Exn.release result
        end) ()

  fun compile config strategy problem =
    case (strategy, problem) of
        (Refute_Eval.Narrowing, Refute_Eval.Pnf _) =>
          compile_problem config strategy problem
      | (Refute_Eval.Narrowing, Refute_Eval.Plans _) =>
          Refute_Eval.Inapplicable
            ["narrowing requires a prenex problem"]
      | (_, Refute_Eval.Pnf _) =>
          Refute_Eval.Inapplicable
            ["narrowing requires the native substrate"]
      | (_, Refute_Eval.Plans _) =>
          compile_problem config strategy problem

  fun dump_native_random_candidates {plan, seed, size, count} =
    case compile Refute_Core.default_config
        (Refute_Eval.Random {seed = seed})
        (Refute_Eval.Plans [Refute_Eval.dump_plan plan]) of
        Refute_Eval.Inapplicable reasons =>
          raise Fail (String.concatWith "; " reasons)
      | Refute_Eval.Compiled test =>
          Refute_Eval.dump_stream test {size = size, count = count}

  val native_substrate : Refute_Eval.substrate =
    {name = "native", priority = 10, compile = compile}

  fun register_substrate () =
    Refute_Eval.register_substrate native_substrate

  val _ = register_substrate ()
end
