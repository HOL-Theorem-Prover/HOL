(*---------------------------------------------------------------------------*)
(*   Overwriting the kernel structures with closed versions.                 *)
(*---------------------------------------------------------------------------*)


structure CoreKernel :> CoreKernel =
struct
  structure Type             = Type
  structure Term             = Term
  structure Tag              = Tag
  structure Thm              = Thm
  structure TheoryPP         = TheoryPP
  structure Theory           = Theory
  structure Definition       = Definition
  structure Net              = Net
end
open CoreKernel;


