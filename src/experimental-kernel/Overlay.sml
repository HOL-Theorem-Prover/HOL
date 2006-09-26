(* ----------------------------------------------------------------------
    Provide standard infixes for rest of distribution

    These infix declarations affect the interactive system as well as
    the "compiled" environment, ensuring a degree of consistency
    between the two.
   ---------------------------------------------------------------------- *)

infix ++ && |-> THEN THEN1 THENL THENC ORELSE ORELSEC THEN_TCL ORELSE_TCL ?>;
infixr ##
infixr 3 -->;
infix 8 via by;

structure Term = Term :> RestrictedTerm where type term = Term.term
structure Tag = Tag :> RestrictedTag where type tag = Tag.tag

