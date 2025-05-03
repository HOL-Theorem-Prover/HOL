(** Based on smlfmt by Sam Westrick, which is released under the MIT license.
  *
  * See the file LICENSE for details.
  *)


datatype Token =
  (** ============ Standard ML ============ *)
  (** ============ core ============ *)
    Abstype
  | And
  | Andalso
  | As
  | Case
  | Datatype
  | Do
  | Else
  | End
  | Exception
  | Fn
  | Fun
  | Handle
  | If
  | In
  | Infix
  | Infixr
  | Let
  | Local
  | Nonfix
  | Of
  | Op
  | Open
  | Orelse
  | Raise
  | Rec
  | Then
  | Type
  | Val
  | With
  | Withtype
  | While
  | OpenParen
  | CloseParen
  | OpenSquareBracket
  | CloseSquareBracket
  | OpenCurlyBracket
  | CloseCurlyBracket
  | Comma
  | Colon
  | Semicolon
  | DotDotDot
  | Underscore
  | Bar
  | Equal
  | FatArrow
  | Arrow
  | Hash
  (** ============ modules ============ *)
  | Eqtype
  | Functor
  | Include
  | Sharing
  | Sig
  | Signature
  | Struct
  | Structure
  | Where
  | ColonArrow
  (** ============ constants ============ *)
  | IntegerConstant
  | WordConstant
  | RealConstant
  | CharConstant
  | StringConstant
  (** ============ identifiers ============ *)
  | Identifier
  | LongIdentifier
  (** ============ trivia ============ *)
  (* Anything that is not part of a token is whitespace - no need to track it
   * explicitly. *)
  | Comment
  | EOF
  (** ============ HOLScript ============ *)
  (** ============ quotes ============ *)
  | HOLOpenQuote  (* ` *) (* ‘ *)
  | HOLCloseQuote  (* ` *) (* ’ *)
  | HOLOpenFullQuote  (* `` *) (* “ *)
  | HOLCloseFullQuote (* `` *) (* ” *)
  | HOLAntiquote  (* ^ within quotations *)
  | HOLComment  (* Comments within quotations *)
  | HOLQuoteContent  (* Anything else within quotations *)
  (** ============ general syntax ============ *)
  (* These tokens must be at the beginning of a line *)
  | HOLCoInductive  (* CoInductive stem: *)
  | HOLDatatype  (* Datatype: *)
  | HOLDefinition  (* Definition defname[attrs]: *)
  | HOLInductive  (* Inductive stem: *)
  | HOLOverload  (* Overload name[attrs] = *)
  | HOLProof  (* Proof *)
  | HOLQED  (* QED *)
  | HOLTermination  (* Termination *)
  | HOLTheorem  (* Theorem name[attrs]: *)
  | HOLSimpleTheorem  (* Theorem name[attrs] = *)
  | HOLTriviality  (* Triviality name[attrs]: *)
  | HOLSimpleTriviality  (* Triviality name[attrs] = *)
  | HOLEnd  (* End *)
  
type token = {
  token: Token,
  start: int,
  stop: int  (* exclusive *)
}
  
  