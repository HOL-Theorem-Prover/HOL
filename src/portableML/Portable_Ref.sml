structure Portable_Ref =
    struct
	fun inc r = r := !r + 1
	fun dec r = r := !r - 1
    end
