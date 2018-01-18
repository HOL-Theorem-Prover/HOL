signature Import =
sig

   datatype monop =
       Abs
     | BNot
     | Bin
     | Cardinality
     | Cast of ParseDatatype.pretype
     | Dec
     | Difference
     | Drop
     | Element
     | FP32To64
     | FP64To32
     | FP64To32_
     | FPAbs of int
     | FPAdd of int
     | FPAdd_ of int
     | FPCmp of int
     | FPDiv of int
     | FPDiv_ of int
     | FPEq of int
     | FPFromInt of int
     | FPGe of int
     | FPGt of int
     | FPIsIntegral of int
     | FPIsFinite of int
     | FPIsNan of int
     | FPIsNormal of int
     | FPIsSignallingNan of int
     | FPIsSubnormal of int
     | FPIsZero of int
     | FPLe of int
     | FPLt of int
     | FPMul of int
     | FPMul_ of int
     | FPMulAdd of int
     | FPMulAdd_ of int
     | FPMulSub of int
     | FPMulSub_ of int
     | FPNeg of int
     | FPRoundToIntegral of int
     | FPSqrt of int
     | FPSqrt_ of int
     | FPSub of int
     | FPSub_ of int
     | FPToInt of int
     | Flat
     | Fst
     | Head
     | Hex
     | IndexOf
     | Intersect
     | IsAlpha
     | IsAlphaNum
     | IsDigit
     | IsHexDigit
     | IsLower
     | IsMember
     | IsSome
     | IsSpace
     | IsSubset
     | IsUpper
     | K1 of ParseDatatype.pretype
     | Length
     | Log
     | Max
     | Min
     | Msb
     | Neg
     | Not
     | PadLeft
     | PadRight
     | QuotRem
     | Remove
     | RemoveExcept
     | RemoveDuplicates
     | Rev
     | SE of ParseDatatype.pretype
     | Size
     | Smax
     | Smin
     | Snd
     | SofL
     | Some
     | Tail
     | Take
     | ToLower
     | ToUpper
     | Union
     | Update
     | ValOf

   datatype binop =
       Add
     | And
     | Asr
     | BAnd
     | BOr
     | BXor
     | Bit
     | Div
     | Exp
     | Fld
     | Ge
     | Gt
     | In
     | Insert
     | Le
     | Lsl
     | Lsr
     | Lt
     | Mod
     | Mul
     | Or
     | Quot
     | Rem
     | Rep
     | Rol
     | Ror
     | SDiv
     | SMod
     | Splitl
     | Splitr
     | Sub
     | Tok
     | Uge
     | Ugt
     | Ule
     | Ult

   val start : string -> unit
   val finish : int -> unit
   val ieee_underflow_before : bool ref

   val Construct : (string * ParseDatatype.constructor list) list -> unit
   val NoBigRecord : string * ParseDatatype.field list -> unit
   val Record : string * ParseDatatype.field list -> unit

   val Def : string * Term.term * Term.term -> Theory.thm
   val Def0 : string * Term.term -> Theory.thm
   val tDef :
      string * Term.term * Term.term * Term.term * Tactic.tactic -> Theory.thm

   val bTy : ParseDatatype.pretype (* bool *)
   val cTy : ParseDatatype.pretype (* char *)
   val fTy : ParseDatatype.pretype (* IEEE flags *)
   val iTy : ParseDatatype.pretype (* int *)
   val nTy : ParseDatatype.pretype (* num *)
   val oTy : ParseDatatype.pretype (* IEEE ordering *)
   val rTy : ParseDatatype.pretype (* IEEE rounding *)
   val sTy : ParseDatatype.pretype (* string *)
   val uTy : ParseDatatype.pretype (* unit/one *)
   val vTy : ParseDatatype.pretype (* bit-string *)

   val CTy : string -> ParseDatatype.pretype
   val VTy : string -> ParseDatatype.pretype
   val FTy : int -> ParseDatatype.pretype
   val F1 : ParseDatatype.pretype
   val F4 : ParseDatatype.pretype
   val F8 : ParseDatatype.pretype
   val F16 : ParseDatatype.pretype
   val F32 : ParseDatatype.pretype
   val F64 : ParseDatatype.pretype
   val BTy : string -> ParseDatatype.pretype
   val ATy : ParseDatatype.pretype * ParseDatatype.pretype ->
             ParseDatatype.pretype
   val PTy : ParseDatatype.pretype * ParseDatatype.pretype ->
             ParseDatatype.pretype
   val LTy : ParseDatatype.pretype -> ParseDatatype.pretype
   val OTy : ParseDatatype.pretype -> ParseDatatype.pretype
   val STy : ParseDatatype.pretype -> ParseDatatype.pretype

   val LU : Term.term
   val LT : Term.term
   val LF : Term.term
   val LI : IntInf.int -> Term.term
   val LN : IntInf.int -> Term.term
   val LSC : char -> Term.term
   val LS : string -> Term.term
   val LV : string -> Term.term
   val LW : IntInf.int * int -> Term.term
   val LY : IntInf.int * string -> Term.term
   val LC : string * ParseDatatype.pretype -> Term.term
   val LE : ParseDatatype.pretype -> Term.term
   val LNL: ParseDatatype.pretype -> Term.term
   val LO : ParseDatatype.pretype -> Term.term
   val LX : ParseDatatype.pretype -> Term.term

   val NEGINF32 : Term.term
   val NEGINF64 : Term.term
   val POSINF32 : Term.term
   val POSINF64 : Term.term
   val NEGZERO32 : Term.term
   val NEGZERO64 : Term.term
   val POSZERO32 : Term.term
   val POSZERO64 : Term.term
   val NEGMIN32 : Term.term
   val NEGMIN64 : Term.term
   val POSMIN32 : Term.term
   val POSMIN64 : Term.term
   val NEGMAX32 : Term.term
   val NEGMAX64 : Term.term
   val POSMAX32 : Term.term
   val POSMAX64 : Term.term
   val QUIETNAN32 : Term.term
   val QUIETNAN64 : Term.term
   val SIGNALNAN32 : Term.term
   val SIGNALNAN64 : Term.term

   val Call : string * ParseDatatype.pretype * Term.term -> Term.term
   val Const : string * ParseDatatype.pretype -> Term.term
   val AVar : ParseDatatype.pretype -> Term.term
   val Var : string * ParseDatatype.pretype -> Term.term
   val bVar : string -> Term.term
   val iVar : string -> Term.term
   val nVar : string -> Term.term
   val sVar : string -> Term.term
   val uVar : string -> Term.term
   val vVar : string -> Term.term
   val Close : Term.term * Term.term -> Term.term
   val Apply : Term.term * Term.term -> Term.term
   val TP : Term.term list -> Term.term
   val Fupd : Term.term * Term.term * Term.term -> Term.term
   val CS : Term.term * (Term.term * Term.term) list -> Term.term
   val Let : Term.term * Term.term * Term.term -> Term.term
   val LL : Term.term list -> Term.term
   val LLC : Term.term list * Term.term -> Term.term
   val SL : Term.term list -> Term.term
   val Rec : ParseDatatype.pretype * Term.term list -> Term.term
   val Dest : string * ParseDatatype.pretype * Term.term -> Term.term
   val Rupd : string * Term.term -> Term.term
   val BL : int * Term.term -> Term.term
   val ITE : Term.term * Term.term * Term.term -> Term.term
   val ITB : (Term.term * Term.term) list * Term.term -> Term.term
   val EX : Term.term * Term.term * Term.term * ParseDatatype.pretype ->
            Term.term
   val BFI : Term.term * Term.term * Term.term * Term.term -> Term.term
   val REP : Term.term * Term.term * ParseDatatype.pretype -> Term.term
   val CC : Term.term list -> Term.term
   val EQ : Term.term * Term.term -> Term.term
   val MU : Term.term * ParseDatatype.pretype -> Term.term
   val MB : Term.term * Term.term -> Term.term
   val MR : Term.term -> Term.term
   val MW : Term.term -> Term.term
   val MN : Term.term * Term.term -> Term.term
   val MD : Term.term * ParseDatatype.pretype -> Term.term
   val For : Term.term -> Term.term
   val Foreach : Term.term -> Term.term
   val Mop : monop * Term.term -> Term.term
   val Bop : binop * Term.term * Term.term -> Term.term

end
