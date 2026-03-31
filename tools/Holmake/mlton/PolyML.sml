structure PolyML =
struct

  structure Compiler = struct
    val compilerVersionNumber = 0
  end

  val pointerEq = MLton.eq

end

structure SML90 =
struct

  exception Interrupt

end

structure Obj =
struct
  (* actually for Moscow ML emulation *)
  fun magic x = Word.toInt (MLton.hash x)
end

exception Interrupt = SML90.Interrupt
