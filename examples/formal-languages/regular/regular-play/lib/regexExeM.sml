open regexEMCML;

structure regexExeM :> regex =
struct

  open regexType;

  fun match r s = regexEMCML.acceptM (regexEMCML.MARK_REG (mapToRegExe r)) (explode s);

end

