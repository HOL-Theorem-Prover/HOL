structure regexDatatypes :> regexDatatypes =
struct

  val Reg_datatype_quot = `Reg =
           Eps
         | Sym 'a
         | Alt Reg Reg
         | Seq Reg Reg
         | Rep Reg`;


  val MReg_datatype_quot = `MReg =
           MEps
         | MSym bool 'a
         | MAlt MReg MReg
         | MSeq MReg MReg
         | MRep MReg`;


  val CMReg_datatype_quot = `CMReg =
           CMEps
         | CMSym      bool 'a
         | CMAlt bool bool CMReg CMReg
         | CMSeq bool bool CMReg CMReg
         | CMRep      bool CMReg`;


end

