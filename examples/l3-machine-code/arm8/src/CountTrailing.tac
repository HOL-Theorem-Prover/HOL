SRW_TAC [] [wordsTheory.LSR_LESS]
THEN Cases_on `w = 0w`
THEN FULL_SIMP_TAC (srw_ss()) [wordsTheory.word_0, wordsTheory.LSR_LESS]
