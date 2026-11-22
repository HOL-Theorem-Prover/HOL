structure Refute_TypeBase :> Refute_TypeBase = struct
  fun theTypeBase () = TypeBase.theTypeBase_of (Refute_Session.context ())

  fun entry_theorems info =
    let
      fun shared (TypeBasePure.ORIG th) = th
        | shared (TypeBasePure.COPY (_, th)) = th
      fun one read = case Lib.total read info of SOME th => [th] | NONE => []
      fun some read =
        case Lib.total read info of SOME (SOME th) => [th] | _ => []
      fun many read = case Lib.total read info of SOME ths => ths | NONE => []
    in
      one (shared o TypeBasePure.axiom_of0) @
      one (shared o TypeBasePure.induction_of0) @
      one TypeBasePure.case_def_of @ one TypeBasePure.case_cong_of @
      one TypeBasePure.case_eq_of @ one TypeBasePure.case_elim_of @
      one TypeBasePure.nchotomy_of @
      some TypeBasePure.one_one_of @ some TypeBasePure.distinct_of @
      some (Option.map (shared o #2) o TypeBasePure.size_of0) @
      some (Option.map (shared o #2) o TypeBasePure.encode_of0) @
      many TypeBasePure.destructors_of @ many TypeBasePure.recognizers_of @
      many TypeBasePure.accessors_of @ many TypeBasePure.updates_of
    end

  fun check_entry info = List.app Refute_Facts.check (entry_theorems info)

  fun fetch ty =
    case TypeBasePure.fetch (theTypeBase ()) ty of
        SOME info => (check_entry info; SOME info)
      | NONE => NONE
  fun peek ty = TypeBasePure.fetch (theTypeBase ()) ty
  fun elts () = TypeBasePure.listItems (theTypeBase ())

  (* The entry of a type, if it has one. *)
  fun check_type ty = ignore (fetch ty) handle Feedback.HOL_ERR _ => ()

  (* [TypeBase]'s own failure for a type it does not know. *)
  fun get name ty =
    case fetch ty of
        SOME info => info
      | NONE =>
          let val {Thy, Tyop, ...} = Type.dest_thy_type ty
          in
            raise Feedback.mk_HOL_ERR "TypeBase" name
              ("unable to find " ^ Lib.quote (Thy ^ "$" ^ Tyop) ^
               " in the TypeBase")
          end

  fun constructors_of ty =
    TypeBasePure.constructors_of (get "constructors_of" ty)
  fun induction_of ty = TypeBasePure.induction_of (get "induction_of" ty)
  fun nchotomy_of ty = TypeBasePure.nchotomy_of (get "nchotomy_of" ty)

  fun range tm = #2 (boolSyntax.strip_fun (Term.type_of tm))

  fun is_constructor tm =
    TypeBasePure.is_constructor (theTypeBase ()) tm andalso
    (check_type (range tm); true)

  (* A pattern's constructors, of whatever type, besides the scrutinee's *)
  fun check_rows scrutinee rows =
    (check_type (Term.type_of scrutinee);
     List.app (fn (pattern, _) =>
       List.app (ignore o is_constructor)
         (HolKernel.find_terms Term.is_const pattern)) rows)

  fun mk_case (scrutinee, rows) =
    (check_rows scrutinee rows;
     TypeBasePure.mk_case (theTypeBase ()) (scrutinee, rows))
  fun is_case tm = TypeBasePure.is_case (theTypeBase ()) tm
  fun strip_case tm =
    let val (scrutinee, rows) = TypeBasePure.strip_case (theTypeBase ()) tm
    in check_rows scrutinee rows; (scrutinee, rows) end
  fun dest_case tm =
    let
      val (case_const, scrutinee, rows) =
        TypeBasePure.dest_case (theTypeBase ()) tm
    in
      check_rows scrutinee rows; (case_const, scrutinee, rows)
    end
  fun is_record tm = TypeBasePure.is_record (theTypeBase ()) tm
  fun dest_record tm =
    let val (ty, fields) = TypeBasePure.dest_record (theTypeBase ()) tm
    in check_type ty; (ty, fields) end

  (* The size of a value of [ty] reads the size theorem of every type
     operator in it. *)
  fun type_size ty =
    let
      fun visit ty =
        if Type.is_vartype ty then ()
        else (check_type ty; List.app visit (#2 (Type.dest_type ty)))
    in
      visit ty; TypeBasePure.type_size (theTypeBase ()) ty
    end
end
