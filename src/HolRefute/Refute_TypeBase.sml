structure Refute_TypeBase :> Refute_TypeBase = struct
  fun theTypeBase () = TypeBase.theTypeBase_of (Refute_Session.context ())

  fun fetch ty = TypeBasePure.fetch (theTypeBase ()) ty
  fun elts () = TypeBasePure.listItems (theTypeBase ())

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

  fun is_constructor tm = TypeBasePure.is_constructor (theTypeBase ()) tm
  fun mk_case x = TypeBasePure.mk_case (theTypeBase ()) x
  fun is_case tm = TypeBasePure.is_case (theTypeBase ()) tm
  fun strip_case tm = TypeBasePure.strip_case (theTypeBase ()) tm
  fun is_record tm = TypeBasePure.is_record (theTypeBase ()) tm
  fun dest_record tm = TypeBasePure.dest_record (theTypeBase ()) tm
end
