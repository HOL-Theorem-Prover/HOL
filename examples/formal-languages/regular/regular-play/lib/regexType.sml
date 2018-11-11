structure regexType :> regexType =
struct

  datatype Reg
       = Eps
       | Sym of char
       | Alt of Reg * Reg
       | Seq of Reg * Reg
       | Rep of Reg

  fun mapToRegExe r =
        case r of
            Eps        => regexEMCML.Eps
          | Sym c      => regexEMCML.Sym c
          | Alt (p, q) => regexEMCML.Alt (mapToRegExe p, mapToRegExe q)
          | Seq (p, q) => regexEMCML.Seq (mapToRegExe p, mapToRegExe q)
          | Rep r      => regexEMCML.Rep (mapToRegExe r)


end

