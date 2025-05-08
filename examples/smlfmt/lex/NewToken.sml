(** Based on smlfmt by Sam Westrick, which is released under the MIT license.
  *
  * See the file LICENSE for details.
  *)

structure NewToken =
struct

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
    | EOF
    (** ============ HOLScript ============ *)
    (** ============ quotes ============ *)
    | HOLOpenQuote  (* ` *) (* ‘ *)
    | HOLCloseQuote  (* ` *) (* ’ *)
    | HOLOpenFullQuote  (* `` *) (* “ *)
    | HOLCloseFullQuote (* `` *) (* ” *)
    | HOLAntiquote  (* ^ within quotations *)
    | HOLQuoteContent  (* Anything else within quotations *)
    | HOLDefinitionLabel  (* [~foo] within quotations *)
    (** ============ general syntax ============ *)
    (* These tokens must be at the beginning of a line *)
    | HOLCoInductive  (* CoInductive stem: *)
    | HOLInductive  (* Inductive stem: *)
    | HOLDatatype  (* Datatype: *)
    | HOLOverload  (* Overload name[attrs] = *)
    | HOLDefinition  (* Definition defname[attrs]: *)
    | HOLTermination  (* Termination *)
    | HOLEnd  (* End *)
    | HOLSimpleTheorem  (* Theorem name[attrs] = *)
    | HOLSimpleTriviality  (* Triviality name[attrs] = *)
    | HOLTheorem  (* Theorem name[attrs]: *)
    | HOLProof  (* Proof *)
    | HOLQED  (* QED *)
    | HOLTriviality  (* Triviality name[attrs]: *)

  type token = {
    token: Token,
    range: Source.range
  }

  type t = token

end
