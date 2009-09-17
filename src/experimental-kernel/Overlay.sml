(* ----------------------------------------------------------------------
    Provide standard infixes for rest of distribution

    These infix declarations affect the interactive system as well as
    the "compiled" environment, ensuring a degree of consistency
    between the two.
   ---------------------------------------------------------------------- *)

infix ++ && |-> THEN THEN1 THENL THENC ORELSE ORELSEC THEN_TCL ORELSE_TCL ?> |>
infixr ##
infixr 3 ==>;
infixr 3 -->;
infix 8 via by;

structure Tag = Tag :> FinalTag where type tag = Tag.tag
structure Kind = Kind :> FinalKind where type kind = Kind.kind
structure Type = Type :> FinalType where type hol_type = Type.hol_type
                                     and type kind = Kind.kind
structure Term = Term :> FinalTerm where type term = Term.term
                                     and type hol_type = Type.hol_type
                                     and type kind = Kind.kind

structure Process = OS.Process
structure FileSys = OS.FileSys

structure PP = HOLPP

type 'a quotation = 'a PP.quotation
type ppstream = PP.ppstream
datatype frag = datatype PP.frag


