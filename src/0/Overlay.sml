(*---------------------------------------------------------------------------*)
(*   Overwriting the kernel structures with closed versions.                 *)
(*---------------------------------------------------------------------------*)


structure CoreKernel :> CoreKernel =
struct
  structure Type       = Type
  structure Term       = Term
  structure Tag        = Tag
  structure Thm        = Thm
  structure TheoryPP   = TheoryPP
  structure Theory     = Theory
  structure Definition = Definition
  structure Net        = Net
end

open CoreKernel;

(* ----------------------------------------------------------------------
    Also provide standard infixes for rest of distribution

    These infix declarations affect the interactive system as well as
    the "compiled" environment, ensuring a degree of consistency
    between the two.
   ---------------------------------------------------------------------- *)

infix ++ && |-> THEN THEN1 THENL THENC ORELSE ORELSEC THEN_TCL ORELSE_TCL ?> |>

(* infixes for THEN shorthands *)
infix >> >- >|

infixr ##;
infixr 3 -->;
infix 8 via by;

structure Process = OS.Process
structure FileSys = OS.FileSys
structure Path    = OS.Path

structure PP = HOLPP

type 'a quotation = 'a PP.quotation
type ppstream = PP.ppstream
datatype frag = datatype PP.frag
