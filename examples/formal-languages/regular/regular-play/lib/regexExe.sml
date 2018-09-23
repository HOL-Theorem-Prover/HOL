open regexEMCML;

structure regexExe :> regex =
struct

  open regexType;

  fun match r s = regexEMCML.accept (mapToRegExe r) (explode s); (*: RegEx -> string -> bool*) 

end

