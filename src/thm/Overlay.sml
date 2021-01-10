(* ----------------------------------------------------------------------
    Provide standard infixes for rest of distribution

    These infix declarations affect the interactive system as well as
    the "compiled" environment, ensuring a degree of consistency
    between the two.
   ---------------------------------------------------------------------- *)

infix ++ && |-> THEN THEN1 THENL THEN_LT THENC ORELSE ORELSE_LT ORELSEC
  THEN_TCL ORELSE_TCL ?> |> |>> ||> ||->
infixr ## ?
infixr 1 $
infixr 3 -->;
infix 8 via by suffices_by
infix 9 using

(* infixes for THEN shorthands *)
infix >> >- >| \\ >>> >>- ?? >~ >>~

infix ~~ !~ Un Isct -- IN -*

signature KERNEL =
sig
  structure Tag : FinalTag
  structure Type : FinalType
  structure Term : FinalTerm where type hol_type = Type.hol_type
  structure Net : FinalNet where type term = Term.term
  structure Thm : Thm where type tag = Tag.tag
                            and type hol_type = Type.hol_type
                            and type term = Term.term
end

structure Kernel :> KERNEL =
struct
  structure Tag = Tag
  structure Type = Type
  structure Term = Term
  structure Net = Net
  structure Thm = Thm
end

open Kernel

structure Process = OS.Process
structure FileSys = OS.FileSys
structure Path    = OS.Path

type 'a quotation = 'a HOLPP.quotation
datatype frag = datatype HOLPP.frag
structure PP = HOLPP
