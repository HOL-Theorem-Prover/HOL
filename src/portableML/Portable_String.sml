structure Portable_String =
    struct
	exception Ord (* = Portable_General.Subscript *)
	open String
	fun ordof (string,place) = Portable_Char.ord(String.sub(string,place))
            handle Subscript => raise Ord
	val charof = str o chr
    end
