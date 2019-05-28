signature Regexp_Match =
sig

 type regexp = Regexp_Type.regexp;

 val normalize : regexp -> regexp
 val nullable : regexp -> bool

 val matcher :
     regexp -> {matchfn : string -> bool,
                start   : int,
                table   : int list list,
                final   : bool list}

 val vector_matcher :
     regexp -> {matchfn: string -> bool,
                table  : int vector vector,
                start  : int,
                final  : bool vector}

 val domBrz : regexp -> unit
end
