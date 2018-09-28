signature regexType =
sig

  datatype Reg
       = Eps
       | Sym of char
       | Alt of Reg * Reg
       | Seq of Reg * Reg
       | Rep of Reg

  val mapToRegExe : Reg -> char regexEMCML.Reg


end

