structure PolyML =
struct

  structure Compiler = struct
    val compilerVersionNumber = 0
  end

  val pointerEq = MLton.eq

end
