Theory ipropSyntax
Ancestors
  hol string

Datatype:
  iprop = IBot
        | IVar string
        | IImp iprop iprop
        | ICnj iprop iprop
        | IDsj iprop iprop
End

val _ = add_strliteral_form {inj = “IVar”, ldelim = "‹"}

Overload ineg = “λp. IImp p Bottom”
Overload "⊤" = “IImp IBot IBot”
Overload "⊥ⁱ" = “IBot”

val _ = set_mapped_fixity {
  term_name = "ICnj", tok = "∧ⁱ", fixity = Infixl 600
}
val _ = set_mapped_fixity {
  term_name = "IDsj", tok = "∨ⁱ", fixity = Infixl 500
}
val _ = set_mapped_fixity {
  term_name = "IImp", tok = "⇒ⁱ", fixity = Infixr 490
}

Definition BiImp_def:
  BiImp A B = (A ⇒ⁱ B) ∧ⁱ (B ⇒ⁱ A)
End

val _ = set_mapped_fixity {
  term_name = "BiImp", tok = "⇔ⁱ", fixity = Infix(NONASSOC, 450)
}
