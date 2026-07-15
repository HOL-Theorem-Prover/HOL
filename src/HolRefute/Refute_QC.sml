structure Refute_QC = struct
  type term = Term.term

  datatype plan =
      Test of term
    | Gen of term * plan
    | Bind of term * term * plan option * plan
    | Split of term * (term * term list * plan) list
    | Guard of term * plan
    | Prune

  fun member tm = List.exists (fn other => Term.aconv tm other)

  fun union_terms left right =
    List.foldl (fn (tm, acc) =>
      if member tm acc then acc else acc @ [tm]) left right

  fun subtract_terms left right =
    List.filter (fn tm => not (member tm right)) left

  fun genspec_available ty =
    ((ignore (Refute_Gen.spec_of ty); true)
     handle Refute_Gen.NoGenerator _ => false)

  fun guarded_gen variable continuation =
    case Refute_Gen.predicate_of (Term.type_of variable) of
      NONE => Gen (variable, continuation)
    | SOME predicate =>
        Gen (variable, Guard (Term.mk_comb (predicate, variable),
          continuation))

  fun gen_all variables continuation =
    List.foldr (fn (variable, plan) => guarded_gen variable plan)
      continuation variables

  fun fully_applied_constructor tm =
    let
      val (constructor, arguments) = boolSyntax.strip_comb tm
      val (domain, _) = boolSyntax.strip_fun (Term.type_of constructor)
    in
      if TypeBase.is_constructor constructor andalso
         length domain = length arguments
      then SOME (constructor, arguments)
      else NONE
    end

  fun fresh_variables avoids types =
    let
      val avoid_variables = List.concat (List.map Term.free_vars_lr avoids)
      fun fresh avoid ty =
        let val variable = Term.variant avoid (Term.mk_var ("x", ty))
        in (variable, avoid @ [variable]) end

      fun loop [] avoid variables = rev variables
        | loop (ty :: rest) avoid variables =
            let val (variable, avoid') = fresh avoid ty
            in loop rest avoid' (variable :: variables) end
    in
      loop types avoid_variables []
    end

  (*
     Plan compilation, ported from exhaustive_generators.ML:260--315.

     compile concl bound [] = gen_all (frees concl \\ bound) (Test concl)
     compile concl bound (a :: rest) =
       if optimise_equality andalso a is (l = r) then
         try_eq (l, r) orelse try_eq (r, l) orelse default
       else default

     try_eq (lhs, x), x a free not in frees(lhs) U bound:
       gen_all (frees a \\ {x})
         (Bind (x, lhs, fallback, compile concl (frees a U bound) rest))
     try_eq (lhs, C a1 ... an), C a fully-applied TypeBase constructor:
       gen_all (frees lhs \\ bound)
         (Split (lhs, [(C, [v1 ... vn],
           compile concl (frees lhs U {vs} U bound)
             ([v1 = a1, ... vn = an] @ rest))]))
     default:
       gen_all (frees a \\ bound)
         (Guard (a, compile concl (frees a U bound) rest))
  *)
  fun compile_plan (config : Refute_Core.config) goal =
    let
      val (assumptions, conclusion) = boolSyntax.strip_imp goal

      fun vars_of bound tm = subtract_terms (Term.free_vars_lr tm) bound

      fun compile conclusion bound assumptions =
        case assumptions of
          [] => gen_all (vars_of bound conclusion) (Test conclusion)
        | assumption :: rest =>
            let
              val assumption_vars = vars_of bound assumption
              val next_bound = union_terms assumption_vars bound
              fun continuation () = compile conclusion next_bound rest

              fun default () =
                gen_all assumption_vars (Guard (assumption, continuation ()))

              fun try_equality (lhs, rhs) =
                if Term.is_var rhs andalso
                   not (member rhs (Term.free_vars_lr lhs)) andalso
                   not (member rhs bound)
                then
                  let
                    val fallback =
                      if genspec_available (Term.type_of rhs) then
                        SOME (guarded_gen rhs (continuation ()))
                      else
                        NONE
                    val variables = subtract_terms assumption_vars [rhs]
                  in
                    SOME (gen_all variables
                      (Bind (rhs, lhs, fallback, continuation ())))
                  end
                else
                  case fully_applied_constructor rhs of
                    NONE => NONE
                  | SOME (constructor, arguments) =>
                      let
                        val lhs_variables = vars_of bound lhs
                        val variables = fresh_variables
                          (conclusion :: assumptions @ bound)
                          (List.map Term.type_of arguments)
                        val equations = ListPair.mapEq boolSyntax.mk_eq
                          (variables, arguments)
                        val branch_bound = union_terms lhs_variables
                          (union_terms variables bound)
                        val branch = compile conclusion branch_bound
                          (equations @ rest)
                      in
                        SOME (gen_all lhs_variables
                          (Split (lhs, [(constructor, variables, branch)])))
                      end
            in
              if #optimise_equality (#qc config) then
                case Lib.total boolSyntax.dest_eq assumption of
                  NONE => default ()
                | SOME (left, right) =>
                    (case try_equality (left, right) of
                       SOME result => result
                     | NONE =>
                         (case try_equality (right, left) of
                            SOME result => result
                          | NONE => default ()))
              else
                default ()
            end
    in
      if #smart_quantifier (#qc config) then
        compile conclusion [] assumptions
      else
        gen_all (Term.free_vars_lr goal) (Test goal)
    end

  fun pp_plan plan =
    let
      fun indent depth = String.implode (List.tabulate (depth, fn _ => #" "))
      fun show depth current =
        case current of
          Test tm => indent depth ^ "Test " ^ Parse.term_to_string tm
        | Gen (variable, continuation) =>
            indent depth ^ "Gen " ^ Parse.term_to_string variable ^ "\n" ^
            show (depth + 2) continuation
        | Bind (variable, expression, fallback, continuation) =>
            indent depth ^ "Bind " ^ Parse.term_to_string variable ^ " = " ^
            Parse.term_to_string expression ^
            (case fallback of NONE => "\n" | SOME plan =>
               "\n" ^ indent (depth + 2) ^ "fallback\n" ^
               show (depth + 4) plan ^ "\n") ^
            show (depth + 2) continuation
        | Split (scrutinee, branches) =>
            let
              fun branch (constructor, variables, continuation) =
                indent (depth + 2) ^ Parse.term_to_string constructor ^ " " ^
                String.concatWith " "
                  (List.map Parse.term_to_string variables) ^
                "\n" ^ show (depth + 4) continuation
            in
              indent depth ^ "Split " ^ Parse.term_to_string scrutinee ^ "\n" ^
              String.concatWith "\n" (List.map branch branches)
            end
        | Guard (predicate, continuation) =>
            indent depth ^ "Guard " ^ Parse.term_to_string predicate ^ "\n" ^
            show (depth + 2) continuation
        | Prune => indent depth ^ "Prune"
    in
      show 0 plan
    end
end
