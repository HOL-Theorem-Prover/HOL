(global-set-key (kbd "C-!") "∀")
(global-set-key (kbd "C-?") "∃")
(global-set-key (kbd "C-&") "∧")
(global-set-key (kbd "C-|") "∨")
(global-set-key (kbd "C-M->") "⇒")
(global-set-key (kbd "C-+") "⇔")
(global-set-key (kbd "C-M-+") "⁺")
(global-set-key (kbd "C-S-u") "∪")
(global-set-key (kbd "C-S-i") "∩")
(global-set-key (kbd "C-:") "∈")
(global-set-key (kbd "C-M-:") "⦂")
(global-set-key (kbd "C-~") (lambda () (interactive) (insert "¬")))
(global-set-key (kbd "C-S-c") "⊆")
(global-set-key (kbd "C-*") (lambda () (interactive) (insert "×")))
(global-set-key (kbd "C-S-q") "≤")
(global-set-key (kbd "C-M-~") "∼")
(global-set-key (kbd "C-M-S-b") "□")
(global-set-key (kbd "C-M-S-m") "◇") ; diaMond

(global-set-key (kbd "C-{") "⟦")
(global-set-key (kbd "C-}") "⟧")
(global-set-key (kbd "C-M-{") "⦃")
(global-set-key (kbd "C-M-}") "⦄")

(define-prefix-command 'hol-unicode-p-map)
(define-prefix-command 'hol-unicode-P-map)
(define-prefix-command 'hol-unicode-not-map)
(define-prefix-command 'hol-unicode-subscript-map)
(define-prefix-command 'hol-unicode-superscript-map)
(define-prefix-command 'hol-unicode-C-map)
(define-prefix-command 'hol-unicode-Q-map)
(define-prefix-command 'hol-unicode-U-map)
(define-prefix-command 'hol-unicode-leftarrow-map)
(define-prefix-command 'hol-unicode-rightarrow-map)
(define-prefix-command 'hol-unicode-lparen-map)
(define-prefix-command 'hol-unicode-rparen-map)
(define-prefix-command 'hol-unicode-shift-map)
(define-prefix-command 'hol-unicode-dquote-map)
(define-prefix-command 'hol-unicode-squote-map)
(define-prefix-command 'hol-unicode-frak-map)
(define-prefix-command 'hol-unicode-calligraphic-map)
(define-prefix-command 'hol-unicode-bboard-map)
(define-prefix-command 'hol-unicode-specialalphabet-map)
(define-key global-map (kbd "C-S-f") 'hol-unicode-shift-map)
(define-key global-map (kbd "C-S-p") 'hol-unicode-p-map)
(define-key global-map (kbd "C-M-S-p") 'hol-unicode-P-map)
(define-key global-map (kbd "C-M-|") 'hol-unicode-not-map)
(define-key global-map (kbd "C-M-_") 'hol-unicode-subscript-map)
(define-key global-map (kbd "C-M-^") 'hol-unicode-superscript-map)
(define-key global-map (kbd "C-S-M-c") 'hol-unicode-C-map)
(define-key global-map (kbd "C-S-M-q") 'hol-unicode-Q-map)
(define-key global-map (kbd "C-S-M-u") 'hol-unicode-U-map)
(define-key global-map (kbd "C-<") 'hol-unicode-leftarrow-map)
(define-key global-map (kbd "C->") 'hol-unicode-rightarrow-map)
(define-key global-map (kbd "C-M-(") 'hol-unicode-lparen-map)
(define-key global-map (kbd "C-M-)") 'hol-unicode-rparen-map)
(define-key global-map (kbd "C-\"") 'hol-unicode-squote-map)
(define-key global-map (kbd "C-M-\"") 'hol-unicode-dquote-map)
(define-key global-map (kbd "C-M-a") 'hol-unicode-specialalphabet-map)

;; Greek : C-S-<char> for lower case version of Greek <char>
;;         add the Meta modifier for upper case Greek letter.
(global-set-key (kbd "C-S-a") "α")
(global-set-key (kbd "C-S-b") "β")
(global-set-key (kbd "C-S-g") "γ")
(global-set-key (kbd "C-S-d") "δ")
(global-set-key (kbd "C-S-e") "ε")
(global-set-key (kbd "C-S-h") "χ")
(global-set-key (kbd "C-S-k") "κ")
(global-set-key (kbd "C-S-l") "λ")
(global-set-key (kbd "C-S-m") "μ")
(global-set-key (kbd "C-S-n") "ν")
(define-key hol-unicode-p-map "i" "π")
(global-set-key (kbd "C-S-o") "ω")
(global-set-key (kbd "C-S-r") "ρ")
(global-set-key (kbd "C-S-s") "σ")
(global-set-key (kbd "C-S-t") "τ")
(global-set-key (kbd "C-S-x") "ξ")
(define-key hol-unicode-p-map "h" "ϕ")  ; U+03D5
(define-key hol-unicode-p-map "v" "φ")  ; U+03C6
(define-key hol-unicode-p-map "s" "ψ")

(global-set-key (kbd "C-S-M-g") "Γ")
(global-set-key (kbd "C-S-M-d") "Δ")
(global-set-key (kbd "C-S-M-l") "Λ")
(global-set-key (kbd "C-S-M-s") "Σ")
(global-set-key (kbd "C-S-M-t") "Θ")
(global-set-key (kbd "C-S-M-o") "Ω")
(global-set-key (kbd "C-S-M-x") "Ξ")
(define-key hol-unicode-P-map "i" "Π")
(define-key hol-unicode-P-map "h" "Φ")
(define-key hol-unicode-P-map "s" "Ψ")

(define-key hol-unicode-not-map "=" "≠")
(define-key hol-unicode-not-map ":" "∉")
(define-key hol-unicode-not-map "0" "∅")
(define-key hol-unicode-not-map "~" "≁")
(define-key hol-unicode-not-map "<" "≮")
(define-key hol-unicode-not-map ">" "≯")
(define-key hol-unicode-not-map (kbd "C-<") "↚")
(define-key hol-unicode-not-map (kbd "C->") "↛")
(define-key hol-unicode-not-map (kbd "C-M-<") "⇍")
(define-key hol-unicode-not-map (kbd "C-M->") "⇏")
(define-key hol-unicode-not-map (kbd "C-S-q") "≰")
(define-key hol-unicode-not-map (kbd "C-+") "⇎")
(define-key hol-unicode-not-map (kbd ",") "◁")

(define-key hol-unicode-subscript-map "1" "₁")
(define-key hol-unicode-subscript-map "2" "₂")
(define-key hol-unicode-subscript-map "3" "₃")
(define-key hol-unicode-subscript-map "4" "₄")
(define-key hol-unicode-subscript-map "5" "₅")
(define-key hol-unicode-subscript-map "6" "₆")
(define-key hol-unicode-subscript-map "7" "₇")
(define-key hol-unicode-subscript-map "8" "₈")
(define-key hol-unicode-subscript-map "9" "₉")
(define-key hol-unicode-subscript-map "0" "₀")
(define-key hol-unicode-subscript-map "a" "ₐ")
(define-key hol-unicode-subscript-map "e" "ₑ")
(define-key hol-unicode-subscript-map "h" "ₕ")
(define-key hol-unicode-subscript-map "i" "ᵢ")
(define-key hol-unicode-subscript-map "j" "ⱼ")
(define-key hol-unicode-subscript-map "k" "ₖ")
(define-key hol-unicode-subscript-map "l" "ₗ")
(define-key hol-unicode-subscript-map "m" "ₘ")
(define-key hol-unicode-subscript-map "n" "ₙ")
(define-key hol-unicode-subscript-map "o" "ₒ")
(define-key hol-unicode-subscript-map "p" "ₚ")
(define-key hol-unicode-subscript-map "r" "ᵣ")
(define-key hol-unicode-subscript-map "s" "ₛ")
(define-key hol-unicode-subscript-map "t" "ₜ")
(define-key hol-unicode-subscript-map "u" "ᵤ")
(define-key hol-unicode-subscript-map "v" "ᵥ")
(define-key hol-unicode-subscript-map "x" "ₓ")
(define-key hol-unicode-subscript-map "+" "₊")
(define-key hol-unicode-subscript-map "=" "₌")
(define-key hol-unicode-subscript-map "-" "₋")

(define-key hol-unicode-superscript-map "1"
  (lambda () (interactive) (insert "¹")))
(define-key hol-unicode-superscript-map "2"
  (lambda () (interactive) (insert "²")))
(define-key hol-unicode-superscript-map "3"
  (lambda () (interactive) (insert "³")))
(define-key hol-unicode-superscript-map "4" "⁴")
(define-key hol-unicode-superscript-map "5" "⁵")
(define-key hol-unicode-superscript-map "6" "⁶")
(define-key hol-unicode-superscript-map "7" "⁷")
(define-key hol-unicode-superscript-map "8" "⁸")
(define-key hol-unicode-superscript-map "9" "⁹")
(define-key hol-unicode-superscript-map "0" "⁰")
(define-key hol-unicode-superscript-map "+" "⁺")
(define-key hol-unicode-superscript-map "-" "⁻")
(define-key hol-unicode-superscript-map "=" "⁼")
(define-key hol-unicode-superscript-map "*" "꙳")

(define-key hol-unicode-superscript-map "A" "ᴬ")
(define-key hol-unicode-superscript-map "B" "ᴮ")
(define-key hol-unicode-superscript-map "D" "ᴰ")
(define-key hol-unicode-superscript-map "E" "ᴱ")
(define-key hol-unicode-superscript-map "G" "ᴳ")
(define-key hol-unicode-superscript-map "H" "ᴴ")
(define-key hol-unicode-superscript-map "I" "ᴵ")
(define-key hol-unicode-superscript-map "J" "ᴶ")
(define-key hol-unicode-superscript-map "K" "ᴷ")
(define-key hol-unicode-superscript-map "L" "ᴸ")
(define-key hol-unicode-superscript-map "M" "ᴹ")
(define-key hol-unicode-superscript-map "N" "ᴺ")
(define-key hol-unicode-superscript-map "O" "ᴼ")
(define-key hol-unicode-superscript-map "P" "ᴾ")
(define-key hol-unicode-superscript-map "R" "ᴿ")
(define-key hol-unicode-superscript-map "T" "ᵀ")
(define-key hol-unicode-superscript-map "U" "ᵁ")
(define-key hol-unicode-superscript-map "V" "ⱽ")
(define-key hol-unicode-superscript-map "W" "ᵂ")
(define-key hol-unicode-superscript-map "a" "ᵃ")
(define-key hol-unicode-superscript-map "b" "ᵇ")
(define-key hol-unicode-superscript-map "c" "ᶜ")
(define-key hol-unicode-superscript-map "d" "ᵈ")
(define-key hol-unicode-superscript-map "e" "ᵉ")
(define-key hol-unicode-superscript-map "f" "ᶠ")
(define-key hol-unicode-superscript-map "g" "ᵍ")
(define-key hol-unicode-superscript-map "h" "ʰ")
(define-key hol-unicode-superscript-map "i" "ⁱ")
(define-key hol-unicode-superscript-map "j" "ʲ")
(define-key hol-unicode-superscript-map "k" "ᵏ")
(define-key hol-unicode-superscript-map "l" "ˡ")
(define-key hol-unicode-superscript-map "m" "ᵐ")
(define-key hol-unicode-superscript-map "n" "ⁿ")
(define-key hol-unicode-superscript-map "o" "ᵒ")
(define-key hol-unicode-superscript-map "p" "ᵖ")
(define-key hol-unicode-superscript-map "r" "ʳ")
(define-key hol-unicode-superscript-map "s" "ˢ")
(define-key hol-unicode-superscript-map "t" "ᵗ")
(define-key hol-unicode-superscript-map "u" "ᵘ")
(define-key hol-unicode-superscript-map "v" "ᵛ")
(define-key hol-unicode-superscript-map "w" "ʷ")
(define-key hol-unicode-superscript-map "x" "ˣ")
(define-key hol-unicode-superscript-map "y" "ʸ")
(define-key hol-unicode-superscript-map "z" "ᶻ")

;; ₀ ₁ ₂ ₃ ₄ ₅ ₆ ₇ ₈ ₉ ₊ ₋ ₌

(define-prefix-command 'hol-unicode-zero-map)
(global-set-key (kbd "C-)") 'hol-unicode-zero-map)
(define-key hol-unicode-zero-map "+" "⊕")
(define-key hol-unicode-zero-map "*" "⊗")
(define-key hol-unicode-zero-map "-" "⊖")
(define-key hol-unicode-zero-map "." "⊙")
(define-key hol-unicode-zero-map "/" "⊘")
(define-key hol-unicode-zero-map "0" "∘") ; U+2218

(define-key hol-unicode-U-map "u" "𝕌")
(define-key hol-unicode-U-map "+" "⊎") ; U+228E "multiset union"
(define-key hol-unicode-U-map "<" "⊌") ; U+228C called simply "multiset", used in HOL for FUNION
(define-key hol-unicode-U-map "p" "Υ") ; Up-silon

; parenthesis map - for various forms of parenthesis
(define-key hol-unicode-lparen-map (kbd "C-M-|") "⦇")
(define-key hol-unicode-rparen-map (kbd "C-M-|") "⦈")
(define-key hol-unicode-lparen-map (kbd "C-M-(") "⦅")
(define-key hol-unicode-rparen-map (kbd "C-M-)") "⦆")
(define-key hol-unicode-lparen-map (kbd "C-<") "⟨")
(define-key hol-unicode-rparen-map (kbd "C->") "⟩")
(define-key hol-unicode-lparen-map (kbd "C-M-<") "⟪")
(define-key hol-unicode-rparen-map (kbd "C-M->") "⟫")
(define-key hol-unicode-lparen-map (kbd "C-M-^") "⎡")
(define-key hol-unicode-rparen-map (kbd "C-M-^") "⎤")
(define-key hol-unicode-lparen-map (kbd "C-M-[") "⦗")
(define-key hol-unicode-rparen-map (kbd "C-M-]") "⦘")

; shift map
(define-key hol-unicode-shift-map (kbd "a") "≫")
(define-key hol-unicode-shift-map (kbd "l") "≪")
(define-key hol-unicode-shift-map (kbd "r") "⋙")

; curly/curvy relational operator map
(define-key hol-unicode-C-map (kbd "_") "⊆")
(define-key hol-unicode-C-map (kbd "-") "≃")
(define-key hol-unicode-C-map (kbd ".") "⪽")
(define-key hol-unicode-C-map (kbd "c") "⊂")
(define-key hol-unicode-C-map (kbd "l") "ℓ")
(define-key hol-unicode-C-map (kbd "p") "⊂")  ; "p" for proper
(define-key hol-unicode-C-map (kbd "q") "≼")  ; "q" for less-or-eQual
(define-key hol-unicode-C-map (kbd "=") "≈")
(define-key hol-unicode-C-map (kbd "+") "≅")
(define-key hol-unicode-C-map (kbd "<") "≺")
(define-key hol-unicode-C-map (kbd "^") "⌢")

; sQuare operators map
(define-key hol-unicode-Q-map (kbd "q") "⊑")
(define-key hol-unicode-Q-map (kbd "<") "⊏")
(define-key hol-unicode-Q-map (kbd "i") "⊓")
(define-key hol-unicode-Q-map (kbd "u") "⊔")
(define-key hol-unicode-Q-map (kbd "/") "⧄")
(define-key hol-unicode-Q-map (kbd "+") "⊞")
(define-key hol-unicode-Q-map (kbd "-") "⊟")
(define-key hol-unicode-Q-map (kbd "*") "⊠")
(define-key hol-unicode-Q-map (kbd ".") "⊡")


; double quotation marks map
(define-key hol-unicode-dquote-map (kbd "C-M-{") "“")
(define-key hol-unicode-dquote-map (kbd "C-M-}") "”")
(define-key hol-unicode-dquote-map (kbd "C-M-<")
  (lambda () (interactive) (insert "«")))
(define-key hol-unicode-dquote-map (kbd "C-M->")
  (lambda () (interactive) (insert "»")))

; single quotation marks map
(define-key hol-unicode-squote-map (kbd "C-{") "‘")
(define-key hol-unicode-squote-map (kbd "C-}") "’")
(define-key hol-unicode-squote-map (kbd "C-<")
  (lambda () (interactive) (insert "‹")))
(define-key hol-unicode-squote-map (kbd "C->")
  (lambda () (interactive) (insert "›")))

(define-key hol-unicode-specialalphabet-map (kbd "c")
  hol-unicode-calligraphic-map)
; calligraphic upper-case map (note numerous special case exceptions)
; app (fn (s1,s2,s3) =>
;        print ("(define-key hol-unicode-calligraphic-map (kbd \"" ^ s1 ^ "\") \"" ^
;               s2 ^ "\")  ; U+" ^ s3 ^ "\n"))
;     (List.tabulate (26, (fn i => (UTF8.chr (i + 65),
;                                   UTF8.chr (i + 0x1D49C),
;                                   Int.fmt StringCvt.HEX (i + 0x1D49C)))));
(define-key hol-unicode-calligraphic-map (kbd "A") "𝒜")  ; U+1D49C
(define-key hol-unicode-calligraphic-map (kbd "B") "ℬ")  ; U+212C
(define-key hol-unicode-calligraphic-map (kbd "C") "𝒞")  ; U+1D49E
(define-key hol-unicode-calligraphic-map (kbd "D") "𝒟")  ; U+1D49F
(define-key hol-unicode-calligraphic-map (kbd "E") "ℰ")  ; U+2130
(define-key hol-unicode-calligraphic-map (kbd "F") "ℱ")  ; U+2131
(define-key hol-unicode-calligraphic-map (kbd "G") "𝒢")  ; U+1D4A2
(define-key hol-unicode-calligraphic-map (kbd "H") "ℋ")  ; U+210B
(define-key hol-unicode-calligraphic-map (kbd "I") "ℐ")  ; U+2110
(define-key hol-unicode-calligraphic-map (kbd "J") "𝒥")  ; U+1D4A5
(define-key hol-unicode-calligraphic-map (kbd "K") "𝒦")  ; U+1D4A6
(define-key hol-unicode-calligraphic-map (kbd "L") "ℒ")  ; U+2112
(define-key hol-unicode-calligraphic-map (kbd "M") "ℳ")  ; U+2113
(define-key hol-unicode-calligraphic-map (kbd "N") "𝒩")  ; U+1D4A9
(define-key hol-unicode-calligraphic-map (kbd "O") "𝒪")  ; U+1D4AA
(define-key hol-unicode-calligraphic-map (kbd "P") "𝒫")  ; U+1D4AB
(define-key hol-unicode-calligraphic-map (kbd "Q") "𝒬")  ; U+1D4AC
(define-key hol-unicode-calligraphic-map (kbd "R") "ℛ")  ; U+211B
(define-key hol-unicode-calligraphic-map (kbd "S") "𝒮")  ; U+1D4AE
(define-key hol-unicode-calligraphic-map (kbd "T") "𝒯")  ; U+1D4AF
(define-key hol-unicode-calligraphic-map (kbd "U") "𝒰")  ; U+1D4B0
(define-key hol-unicode-calligraphic-map (kbd "V") "𝒱")  ; U+1D4B1
(define-key hol-unicode-calligraphic-map (kbd "W") "𝒲")  ; U+1D4B2
(define-key hol-unicode-calligraphic-map (kbd "X") "𝒳")  ; U+1D4B3
(define-key hol-unicode-calligraphic-map (kbd "Y") "𝒴")  ; U+1D4B4
(define-key hol-unicode-calligraphic-map (kbd "Z") "𝒵")  ; U+1D4B5
; app (fn (s1,s2,s3) =>
;        print ("(define-key hol-unicode-calligraphic-map (kbd \"" ^ s1 ^ "\") \"" ^
;               s2 ^ "\")  ; U+" ^ s3 ^ "\n"))
;     (List.tabulate (26, (fn i => (UTF8.chr (i + 97),
;                                   UTF8.chr (i + 0x1D4B6),
;                                   Int.fmt StringCvt.HEX (i + 0x1D4B6)))));
(define-key hol-unicode-calligraphic-map (kbd "a") "𝒶")  ; U+1D4B6
(define-key hol-unicode-calligraphic-map (kbd "b") "𝒷")  ; U+1D4B7
(define-key hol-unicode-calligraphic-map (kbd "c") "𝒸")  ; U+1D4B8
(define-key hol-unicode-calligraphic-map (kbd "d") "𝒹")  ; U+1D4B9
(define-key hol-unicode-calligraphic-map (kbd "e") "ℯ")  ; U+212F
(define-key hol-unicode-calligraphic-map (kbd "f") "𝒻")  ; U+1D4BB
(define-key hol-unicode-calligraphic-map (kbd "g") "ℊ")  ; U+210A
(define-key hol-unicode-calligraphic-map (kbd "h") "𝒽")  ; U+1D4BD
(define-key hol-unicode-calligraphic-map (kbd "i") "𝒾")  ; U+1D4BE
(define-key hol-unicode-calligraphic-map (kbd "j") "𝒿")  ; U+1D4BF
(define-key hol-unicode-calligraphic-map (kbd "k") "𝓀")  ; U+1D4C0
(define-key hol-unicode-calligraphic-map (kbd "l") "𝓁")  ; U+1D4C1
(define-key hol-unicode-calligraphic-map (kbd "m") "𝓂")  ; U+1D4C2
(define-key hol-unicode-calligraphic-map (kbd "n") "𝓃")  ; U+1D4C3
(define-key hol-unicode-calligraphic-map (kbd "o") "ℴ")  ; U+2134
(define-key hol-unicode-calligraphic-map (kbd "p") "𝓅")  ; U+1D4C5
(define-key hol-unicode-calligraphic-map (kbd "q") "𝓆")  ; U+1D4C6
(define-key hol-unicode-calligraphic-map (kbd "r") "𝓇")  ; U+1D4C7
(define-key hol-unicode-calligraphic-map (kbd "s") "𝓈")  ; U+1D4C8
(define-key hol-unicode-calligraphic-map (kbd "t") "𝓉")  ; U+1D4C9
(define-key hol-unicode-calligraphic-map (kbd "u") "𝓊")  ; U+1D4CA
(define-key hol-unicode-calligraphic-map (kbd "v") "𝓋")  ; U+1D4CB
(define-key hol-unicode-calligraphic-map (kbd "w") "𝓌")  ; U+1D4CC
(define-key hol-unicode-calligraphic-map (kbd "x") "𝓍")  ; U+1D4CD
(define-key hol-unicode-calligraphic-map (kbd "y") "𝓎")  ; U+1D4CE
(define-key hol-unicode-calligraphic-map (kbd "z") "𝓏")  ; U+1D4CF



(define-key hol-unicode-specialalphabet-map (kbd "f") hol-unicode-frak-map)
; fraktur map
; app (fn (s1,s2,s3) =>
;        print ("(define-key hol-unicode-frak-map (kbd \"" ^ s1 ^ "\") \"" ^
;               s2 ^ "\")  ; U+" ^ s3 ^ "\n"))
;     (List.tabulate (26, (fn i => (UTF8.chr (i + 65),
;                                   UTF8.chr (i + 0x1D56C),
;                                   Int.fmt StringCvt.HEX (i + 0x1D56C)))));
(define-key hol-unicode-frak-map (kbd "A") "𝕬")  ; U+1D56C
(define-key hol-unicode-frak-map (kbd "B") "𝕭")  ; U+1D56D
(define-key hol-unicode-frak-map (kbd "C") "𝕮")  ; U+1D56E
(define-key hol-unicode-frak-map (kbd "D") "𝕯")  ; U+1D56F
(define-key hol-unicode-frak-map (kbd "E") "𝕰")  ; U+1D570
(define-key hol-unicode-frak-map (kbd "F") "𝕱")  ; U+1D571
(define-key hol-unicode-frak-map (kbd "G") "𝕲")  ; U+1D572
(define-key hol-unicode-frak-map (kbd "H") "𝕳")  ; U+1D573
(define-key hol-unicode-frak-map (kbd "I") "𝕴")  ; U+1D574
(define-key hol-unicode-frak-map (kbd "J") "𝕵")  ; U+1D575
(define-key hol-unicode-frak-map (kbd "K") "𝕶")  ; U+1D576
(define-key hol-unicode-frak-map (kbd "L") "𝕷")  ; U+1D577
(define-key hol-unicode-frak-map (kbd "M") "𝕸")  ; U+1D578
(define-key hol-unicode-frak-map (kbd "N") "𝕹")  ; U+1D579
(define-key hol-unicode-frak-map (kbd "O") "𝕺")  ; U+1D57A
(define-key hol-unicode-frak-map (kbd "P") "𝕻")  ; U+1D57B
(define-key hol-unicode-frak-map (kbd "Q") "𝕼")  ; U+1D57C
(define-key hol-unicode-frak-map (kbd "R") "𝕽")  ; U+1D57D
(define-key hol-unicode-frak-map (kbd "S") "𝕾")  ; U+1D57E
(define-key hol-unicode-frak-map (kbd "T") "𝕿")  ; U+1D57F
(define-key hol-unicode-frak-map (kbd "U") "𝖀")  ; U+1D580
(define-key hol-unicode-frak-map (kbd "V") "𝖁")  ; U+1D581
(define-key hol-unicode-frak-map (kbd "W") "𝖂")  ; U+1D582
(define-key hol-unicode-frak-map (kbd "X") "𝖃")  ; U+1D583
(define-key hol-unicode-frak-map (kbd "Y") "𝖄")  ; U+1D584
(define-key hol-unicode-frak-map (kbd "Z") "𝖅")  ; U+1D585
; app (fn (s1,s2,s3) =>
;        print ("(define-key hol-unicode-frak-map (kbd \"" ^ s1 ^ "\") \"" ^
;               s2 ^ "\")  ; U+" ^ s3 ^ "\n"))
;     (List.tabulate (26, (fn i => (UTF8.chr (i + 97),
;                                   UTF8.chr (i + 0x1D586),
;                                   Int.fmt StringCvt.HEX (i + 0x1D586)))));
(define-key hol-unicode-frak-map (kbd "a") "𝖆")  ; U+1D586
(define-key hol-unicode-frak-map (kbd "b") "𝖇")  ; U+1D587
(define-key hol-unicode-frak-map (kbd "c") "𝖈")  ; U+1D588
(define-key hol-unicode-frak-map (kbd "d") "𝖉")  ; U+1D589
(define-key hol-unicode-frak-map (kbd "e") "𝖊")  ; U+1D58A
(define-key hol-unicode-frak-map (kbd "f") "𝖋")  ; U+1D58B
(define-key hol-unicode-frak-map (kbd "g") "𝖌")  ; U+1D58C
(define-key hol-unicode-frak-map (kbd "h") "𝖍")  ; U+1D58D
(define-key hol-unicode-frak-map (kbd "i") "𝖎")  ; U+1D58E
(define-key hol-unicode-frak-map (kbd "j") "𝖏")  ; U+1D58F
(define-key hol-unicode-frak-map (kbd "k") "𝖐")  ; U+1D590
(define-key hol-unicode-frak-map (kbd "l") "𝖑")  ; U+1D591
(define-key hol-unicode-frak-map (kbd "m") "𝖒")  ; U+1D592
(define-key hol-unicode-frak-map (kbd "n") "𝖓")  ; U+1D593
(define-key hol-unicode-frak-map (kbd "o") "𝖔")  ; U+1D594
(define-key hol-unicode-frak-map (kbd "p") "𝖕")  ; U+1D595
(define-key hol-unicode-frak-map (kbd "q") "𝖖")  ; U+1D596
(define-key hol-unicode-frak-map (kbd "r") "𝖗")  ; U+1D597
(define-key hol-unicode-frak-map (kbd "s") "𝖘")  ; U+1D598
(define-key hol-unicode-frak-map (kbd "t") "𝖙")  ; U+1D599
(define-key hol-unicode-frak-map (kbd "u") "𝖚")  ; U+1D59A
(define-key hol-unicode-frak-map (kbd "v") "𝖛")  ; U+1D59B
(define-key hol-unicode-frak-map (kbd "w") "𝖜")  ; U+1D59C
(define-key hol-unicode-frak-map (kbd "x") "𝖝")  ; U+1D59D
(define-key hol-unicode-frak-map (kbd "y") "𝖞")  ; U+1D59E
(define-key hol-unicode-frak-map (kbd "z") "𝖟")  ; U+1D59F


; blackboard map
(define-key hol-unicode-specialalphabet-map (kbd "b") hol-unicode-bboard-map)
;app (fn (s1,s2,s3) =>
;       print ("(define-key hol-unicode-bboard-map (kbd \"" ^ s1 ^ "\") \"" ^
;              s2 ^ "\")  ; U+" ^ s3 ^ "\n"))
;    (List.tabulate (26, (fn i => (UTF8.chr (i + 65),
;                                  UTF8.chr (i + 0x1D538),
;                                  Int.fmt StringCvt.HEX (i + 0x1D538)))))
; except special cases: C, H, N, P, Q, R and Z
(define-key hol-unicode-bboard-map (kbd "A") "𝔸")  ; U+1D538
(define-key hol-unicode-bboard-map (kbd "B") "𝔹")  ; U+1D539
(define-key hol-unicode-bboard-map (kbd "C") "ℂ")  ; U+2102
(define-key hol-unicode-bboard-map (kbd "D") "𝔻")  ; U+1D53B
(define-key hol-unicode-bboard-map (kbd "E") "𝔼")  ; U+1D53C
(define-key hol-unicode-bboard-map (kbd "F") "𝔽")  ; U+1D53D
(define-key hol-unicode-bboard-map (kbd "G") "𝔾")  ; U+1D53E
(define-key hol-unicode-bboard-map (kbd "H") "ℍ")  ; U+210D
(define-key hol-unicode-bboard-map (kbd "I") "𝕀")  ; U+1D540
(define-key hol-unicode-bboard-map (kbd "J") "𝕁")  ; U+1D541
(define-key hol-unicode-bboard-map (kbd "K") "𝕂")  ; U+1D542
(define-key hol-unicode-bboard-map (kbd "L") "𝕃")  ; U+1D543
(define-key hol-unicode-bboard-map (kbd "M") "𝕄")  ; U+1D544
(define-key hol-unicode-bboard-map (kbd "N") "ℕ")  ; U+1D545
(define-key hol-unicode-bboard-map (kbd "O") "𝕆")  ; U+1D546
(define-key hol-unicode-bboard-map (kbd "P") "ℙ")  ; U+1D547
(define-key hol-unicode-bboard-map (kbd "Q") "ℚ")  ; U+1D548
(define-key hol-unicode-bboard-map (kbd "R") "ℝ")  ; U+1D549
(define-key hol-unicode-bboard-map (kbd "S") "𝕊")  ; U+1D54A
(define-key hol-unicode-bboard-map (kbd "T") "𝕋")  ; U+1D54B
(define-key hol-unicode-bboard-map (kbd "U") "𝕌")  ; U+1D54C
(define-key hol-unicode-bboard-map (kbd "V") "𝕍")  ; U+1D54D
(define-key hol-unicode-bboard-map (kbd "W") "𝕎")  ; U+1D54E
(define-key hol-unicode-bboard-map (kbd "X") "𝕏")  ; U+1D54F
(define-key hol-unicode-bboard-map (kbd "Y") "𝕐")  ; U+1D550
(define-key hol-unicode-bboard-map (kbd "Z") "ℤ")  ; U+1D551
; and numbers
(dotimes (i 10)
  (define-key hol-unicode-bboard-map (kbd (format "%d" i))
    (char-to-string (+ i #x1d7d8))))



; arrow maps
(define-key hol-unicode-leftarrow-map (kbd "-") "←")
(define-key hol-unicode-leftarrow-map (kbd "C-<") "↞")
(define-key hol-unicode-leftarrow-map (kbd "C->") "↔")
(define-key hol-unicode-leftarrow-map (kbd "<") "↢")
(define-key hol-unicode-leftarrow-map (kbd "|") "↤")
(define-key hol-unicode-leftarrow-map (kbd "`") "↼")
(define-key hol-unicode-leftarrow-map (kbd ",") "↽")
(define-key hol-unicode-leftarrow-map (kbd ".") "⇠")
(define-key hol-unicode-leftarrow-map (kbd "=") "⇐")
(define-key hol-unicode-leftarrow-map (kbd "a") "↫")
(define-key hol-unicode-leftarrow-map (kbd "c") "↩")
(define-key hol-unicode-leftarrow-map (kbd "w") "⇜")
(define-key hol-unicode-leftarrow-map (kbd "~") "↜")

(define-key hol-unicode-rightarrow-map (kbd "-") "→")
(define-key hol-unicode-rightarrow-map (kbd "C->") "↠")
(define-key hol-unicode-rightarrow-map (kbd ">") "↣")
(define-key hol-unicode-rightarrow-map (kbd "|") "↦")
(define-key hol-unicode-rightarrow-map (kbd "`") "⇀")
(define-key hol-unicode-rightarrow-map (kbd ",") "⇁")
(define-key hol-unicode-rightarrow-map (kbd ".") "⇢")
(define-key hol-unicode-rightarrow-map (kbd "=") "⇒")
(define-key hol-unicode-rightarrow-map (kbd "a") "↬")
(define-key hol-unicode-rightarrow-map (kbd "c") "↪")
(define-key hol-unicode-rightarrow-map (kbd "w") "⇝")
(define-key hol-unicode-rightarrow-map (kbd "~") "↝")
