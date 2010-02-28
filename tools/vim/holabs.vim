iab /\ ∧
iab \/ ∨
iab ~ ¬
iab ==> ⇒
iab <= ≤
iab >= ≥
iab <=> ⇔
iab <> ≠
iab ! ∀
iab ? ∃
iab \ λ
iab IN ∈
iab NOTIN ∉
iab UNION ∪
iab SUBSET ⊆
set iskeyword+=>,/
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
  s/⊆/SUBSET/eg
endf
