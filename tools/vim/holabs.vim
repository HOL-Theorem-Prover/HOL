iab /\ ∧
iab \/ ∨
iab ~ ¬
iab .~ .¬
iab ==> ⇒
iab <= ≤
iab >= ≥
iab <=> ⇔
iab <> ≠
iab ! ∀
iab ? ∃
iab \\ λ
iab `! `∀
iab `? `∃
iab `\ `λ
iab (! (∀
iab (? (∃
iab (\ (λ
iab .! .∀
iab .? .∃
iab IN ∈
iab NOTIN ∉
iab UNION ∪
set iskeyword+=!,<,=,>,~
fu! HOLUnab ()
  s/∧/\/\\/eg
  s/∨/\\\//eg
  s/¬/~/eg
  s/⇒/==>/eg
  s/≤/<=/eg
  s/≥/>=/eg
  s/⇔/<=>/eg
  s/≠/<>/eg
  s/∀/!/eg
  s/∃/?/eg
  s/λ/\\/eg
  s/∈/IN/eg
  s/∉/NOTIN/eg
  s/∪/UNION/eg
endf
