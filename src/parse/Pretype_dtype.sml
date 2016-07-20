structure Pretype_dtype =
struct

 datatype pretype
    = Vartype of string
    | Tyop of {Thy:string,Tyop:string, Args: pretype list}
    | UVar of int

end
