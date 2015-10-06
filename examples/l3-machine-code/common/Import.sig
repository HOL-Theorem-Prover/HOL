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
     | FPAbs of int
     | FPAdd of int
     | FPEqual of int
     | FPIsNaN of int
     | FPLess of int
     | FPMul of int
     | FPNeg of int
     | FPSub of int
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
     | Mdfy
     | Mod
     | Mul
     | Or
     | Quot
     | Rem
     | Rep
     | Rol
     | Ror
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

   val Record : string * ParseDatatype.field list -> unit
   val Construct : (string * ParseDatatype.constructor list) list -> unit
   val Def : string * Term.term * Term.term -> Theory.thm
   val tDef :
      string * Term.term * Term.term * Term.term * Tactic.tactic -> Theory.thm
   val Def0 : string * Term.term -> Theory.thm

   val bTy : ParseDatatype.pretype
   val iTy : ParseDatatype.pretype
   val nTy : ParseDatatype.pretype
   val rTy : ParseDatatype.pretype
   val cTy : ParseDatatype.pretype
   val sTy : ParseDatatype.pretype
   val uTy : ParseDatatype.pretype
   val vTy : ParseDatatype.pretype

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
   val LI : int -> Term.term
   val LN : int -> Term.term
   val LSC : char -> Term.term
   val LS : string -> Term.term
   val LV : string -> Term.term
   val LW : int * int -> Term.term
   val LY : int * string -> Term.term
   val LC : string * ParseDatatype.pretype -> Term.term
   val LE : ParseDatatype.pretype -> Term.term
   val LNL: ParseDatatype.pretype -> Term.term
   val LO : ParseDatatype.pretype -> Term.term
   val LX : ParseDatatype.pretype -> Term.term

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
