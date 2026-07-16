structure Refute_EvalSML = struct
  type term = Term.term

  exception Stuck of string

  type reconstruction = unit -> term
  type generated_hit = (int * reconstruction) list * bool
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
  val constructors : term vector ref = ref (Vector.fromList [])
  val raw_terms : term vector ref = ref (Vector.fromList [])
  val table_serial = ref 0
  val term_tables = ref
    ([] : (int * term vector * term vector) list)
  val table_mutex = Mutex.mutex ()
  val reconstruction_forces = ref 0

  fun note_force () =
    reconstruction_forces := !reconstruction_forces + 1

  fun reset_reconstruction_forces () = reconstruction_forces := 0

  fun install_constructors terms =
    constructors := Vector.fromList terms

  fun install_raw_terms terms =
    raw_terms := Vector.fromList terms

  fun register_term_tables constructor_terms terms =
    let
      val serial = !table_serial
      val _ = table_serial := serial + 1
      val entry =
        (serial, Vector.fromList constructor_terms, Vector.fromList terms)
      val _ = term_tables := entry :: !term_tables
    in
      serial
    end

  fun with_term_tables serial action =
    let
      val (_, constructor_table, term_table) =
        valOf (List.find (fn (index, _, _) => index = serial)
          (!term_tables))
      fun body () =
        let
          val old_constructors = !constructors
          val old_terms = !raw_terms
          val result = Exn.capture (fn () =>
            (constructors := constructor_table;
             raw_terms := term_table;
             action ())) ()
          val _ = constructors := old_constructors
          val _ = raw_terms := old_terms
        in
          Exn.release result
        end
    in
      Thread_Attributes.uninterruptible
        (fn restore => fn () =>
          let
            val _ = Mutex.lock table_mutex
            val result = Exn.capture (restore body) ()
            val _ = Mutex.unlock table_mutex
          in
            Exn.release result
          end) ()
    end

  fun wrap_reconstruction serial rebuild () =
    with_term_tables serial rebuild

  fun table_term serial index =
    with_term_tables serial (fn () => Vector.sub (!raw_terms, index))

  fun raw_term index =
    (note_force (); Vector.sub (!raw_terms, index))

  fun con_term index arguments =
    (note_force ();
     Term.list_mk_comb (Vector.sub (!constructors, index), arguments))

  fun num_term value =
    (note_force ();
     numSyntax.mk_numeral
       (Arbnum.fromString (IntInf.toString value)))

  fun int_term value =
    (note_force ();
     intSyntax.term_of_int
       (Arbint.fromString (IntInf.toString value)))

  fun char_term character =
    (note_force ();
     stringSyntax.mk_chr
       (numSyntax.term_of_int (Char.ord character)))

  fun string_term text =
    (note_force (); stringSyntax.fromMLstring text)

  fun word_term width value =
    (note_force ();
     wordsSyntax.mk_wordi
       (Arbnum.fromString (IntInf.toString value), width))

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
      #2 (boolSyntax.dest_eq (Thm.concl theorem))
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
end
