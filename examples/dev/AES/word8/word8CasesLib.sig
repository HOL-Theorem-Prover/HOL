signature word8CasesLib = sig

include Abbrev

 val word8Define : term quotation -> thm
 val word8Cases_on : term quotation -> tactic

end