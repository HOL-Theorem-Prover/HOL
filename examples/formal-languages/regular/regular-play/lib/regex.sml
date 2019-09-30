structure regex :> regex =
struct

  open regexType;

  fun match (r:Reg) (s:string) = raise Match;

end

