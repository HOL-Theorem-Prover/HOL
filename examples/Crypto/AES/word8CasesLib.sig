signature word8CasesLib = sig

include Abbrev

 val word8Define : term quotation -> thm
 val word8Cases_on : term quotation -> tactic
 val word8GenCases : term quotation -> (term -> thm) -> (thm * thm)

end
