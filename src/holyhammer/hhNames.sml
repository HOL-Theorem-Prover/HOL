(* ========================================================================= *)
(* FILE          : hhNames.sml                                               *)
(* DESCRIPTION   : Supplies of fresh type variables for problem generation   *)
(* AUTHOR        : Lukasz Czajka                                             *)
(* ========================================================================= *)

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
      val owner : Thread.thread option ref = ref NONE
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
                  Portable.bracket
                    (fn () => owner := SOME (Thread.self ()))
                    (fn () => owner := NONE) (fn () => f ())) ()) ()
      fun supply () =
        let val current = !next in
          if (case !owner of
                  SOME t => Thread.equal (t, Thread.self ())
                | NONE => false) then ()
          else raise Fail "hhNames: a private supply is used outside scoped, \
                          \or from a thread other than its scoped one";
          next := current + 1;
          Type.mk_vartype (prefix ^ Int.toString current)
        end
      (* The global counter has handed out everything below the number of
         its next draw.  It is monotone and advances by one per draw, so
         after reading the number k of one draw, the draws up to the number
         !next - 1 are the next (!next - 1 - k) ones, which need no
         parsing.  (A check by a further draw would itself move the
         counter, so there is none.) *)
      fun release () =
        let
          val (_, k) = draw ()
          val missing = !next - 1 - k
          fun skip n =
            if n <= 0 then () else (ignore (Type.gen_tyvar ()); skip (n - 1))
        in
          skip missing
        end
    in
      {supply = supply, release = release, scoped = scoped}
    end

end
