open regexEMCML;

structure regexExeMC :> regex =
struct

  open regexType;

  fun match r s = regexEMCML.acceptCM (regexEMCML.CACHE_REG (regexEMCML.MARK_REG (mapToRegExe r))) (explode s);

end

