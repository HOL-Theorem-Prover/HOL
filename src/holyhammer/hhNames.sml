structure hhNames :> hhNames =
struct

  type supply = unit -> Type.hol_type

  val global : supply = Type.gen_tyvar

  fun number name = valOf (Type.gen_tyvar_number name)

  fun private_supply () =
    let
      val next = ref (number (Type.gen_tyvar ()))
      fun supply () =
        let val current = !next in
          next := current + 1;
          Type.mk_gen_tyvar current
        end
      (* The global counter has handed out everything below the number of
         its next draw; draw until that number is past the last one used. *)
      fun release () =
        if number (Type.gen_tyvar ()) >= !next - 1 then () else release ()
    in
      {supply = supply, release = release}
    end

end
