(*---------------------------------------------------------------------------*)
(*   Overwriting the kernel structures with closed versions.                 *)
(*---------------------------------------------------------------------------*)

structure Type : Type             = Type
structure Term : Term             = Term
structure Tag  : Tag              = Tag
structure Thm  : Thm              = Thm
structure TheoryPP : TheoryPP     = TheoryPP
structure Theory : Theory         = Theory
structure Definition : Definition = Definition
structure Net : Net               = Net

structure KernelTypes = struct end;
