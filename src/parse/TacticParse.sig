signature TacticParse =
sig

type 'a delim = int * int * 'a
datatype expr
  = EmptyE
  | ParenE of expr delim * bool
  | TupleE of expr delim list * bool
  | ListE of expr delim list * bool
  | IdentE of string
  | OpaqueE
  | InfixE of expr delim * string delim * expr delim
  | AppE of expr delim list

val getPrec: expr -> int

val parseSMLSimple: string -> int * int * expr

datatype 'a tac_expr
  = Then of 'a tac_expr list
  | ThenLT of 'a tac_expr * 'a tac_expr list
  | Subgoal of 'a
  | First of 'a tac_expr list
  | Try of 'a tac_expr
  | Repeat of 'a tac_expr
  | MapEvery of 'a * 'a tac_expr list
  | MapFirst of 'a * 'a tac_expr list
  | Rename of 'a
  | Opaque of int * 'a

  | LThen of 'a tac_expr * 'a tac_expr list
  | LThenLT of 'a tac_expr list
  | LThen1 of 'a tac_expr
  | LTacsToLT of 'a tac_expr
  | LNullOk of 'a tac_expr
  | LFirst of 'a tac_expr list
  | LFirstLT of 'a tac_expr
  | LSelectGoal of 'a
  | LSelectGoals of 'a
  | LAllGoals of 'a tac_expr
  | LNthGoal of 'a tac_expr * 'a
  | LLastGoal of 'a tac_expr
  | LHeadGoal of 'a tac_expr
  | LSplit of 'a * 'a tac_expr * 'a tac_expr
  | LReverse
  | LTry of 'a tac_expr
  | LRepeat of 'a tac_expr
  | LSelectThen of 'a tac_expr * 'a tac_expr
  | LOpaque of int * 'a

  | List of 'a * 'a tac_expr list
  | Group of bool * 'a * 'a tac_expr
  | RepairEmpty of bool * 'a * string
  | RepairGroup of 'a * string * 'a tac_expr * string
  | OOpaque of int * 'a

val isTac: 'a tac_expr -> bool
val topSpan: 'a tac_expr -> 'a option

val parseTacticBlock: string -> (int * int) tac_expr

val mapTacExpr:
  { start: bool -> 'a -> 'b, stop: bool -> 'b -> 'c,
    repair: 'a -> string -> unit } ->
  'a tac_expr -> 'c tac_expr

val printTacsAsE: string -> (int * int) tac_expr list -> string

datatype tac_frag_open
  = FOpen
  | FOpenThen1
  | FOpenFirst
  | FOpenRepeat
  | FOpenTacsToLT
  | FOpenNullOk
  | FOpenNthGoal of int * int
  | FOpenLastGoal
  | FOpenHeadGoal
  | FOpenSplit of int * int
  | FOpenSelect
  | FOpenFirstLT

datatype tac_frag_mid
  = FNextFirst
  | FNextTacsToLT
  | FNextSplit
  | FNextSelect

datatype tac_frag_close
  = FClose
  | FCloseFirst
  | FCloseRepeat
  | FCloseFirstLT

datatype tac_frag
  = FFOpen of tac_frag_open
  | FFMid of tac_frag_mid
  | FFClose of tac_frag_close
  | FAtom of (int * int) tac_expr
  | FGroup of (int * int) * tac_frag list
  | FBracket of
    tac_frag_open * tac_frag list * tac_frag_close * (int * int) tac_expr
  | FMBracket of
    tac_frag_open * tac_frag_mid * tac_frag_close *
    tac_frag list list * (int * int) tac_expr

val linearize: ((int * int) tac_expr -> bool) ->
  (int * int) tac_expr -> tac_frag list

val unlinearize: tac_frag list -> (int * int) tac_expr

val printFragsAsE: string -> tac_frag list list -> string

val sliceTacticBlock:
  int -> int -> bool -> int * int -> (int * int) tac_expr -> tac_frag list list

end
