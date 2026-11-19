structure hhNames :> hhNames =
struct

  type supply = unit -> Type.hol_type

  val global : supply = Type.gen_tyvar

  (* A generated name is a fixed prefix followed by the decimal number of
     the draw.  The prefix is not exported by the kernel; it is the name of
     a drawn variable without its trailing digits. *)
  fun split_name name =
    let
      val digits = String.size name -
        Substring.size (Substring.dropr Char.isDigit (Substring.full name))
      val prefix = String.substring (name, 0, String.size name - digits)
      val tail = String.extract (name, String.size name - digits, NONE)
    in
      if digits = 0 then raise Fail ("hhNames: no number in " ^ name)
      else (prefix, valOf (Int.fromString tail))
    end

  fun draw () = split_name (Type.dest_vartype (Type.gen_tyvar ()))

  fun private_supply () =
    let
      val (prefix, first) = draw ()
      val next = ref first
      val inside = ref false
      (* The kernel's Type.mk_vartype complains about a non-standard name
         unless the trace Vartype_Format_Complaint is off.  Flags are
         per-thread only inside a pin (Context.with_context): an unpinned
         with_bflags writes the live cell that every thread reads, so a
         scope that turns the trace off is pinned. *)
      fun scoped f =
        Context.with_context (Context.snapshot ())
          (fn () =>
             HOLFlags.with_bflags [(Type.vartype_fmt_complaint, false)]
               (fn () =>
                  Portable.bracket (fn () => inside := true)
                    (fn () => inside := false) (fn () => f ())) ()) ()
      fun supply () =
        let val current = !next in
          if !inside then ()
          else raise Fail "hhNames: a private supply is used outside scoped";
          next := current + 1;
          Type.mk_vartype (prefix ^ Int.toString current)
        end
      (* The global counter has handed out everything below the number of
         its next draw; draw until that number is past the last one used. *)
      fun release () =
        if #2 (draw ()) >= !next - 1 then () else release ()
    in
      {supply = supply, release = release, scoped = scoped}
    end

end
