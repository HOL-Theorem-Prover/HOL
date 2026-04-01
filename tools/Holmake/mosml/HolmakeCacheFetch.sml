structure HolmakeCacheFetch =
struct

fun fetch _ _ talk = let
    val _ = talk "cache fetching is not supported with mosml-built Holmake"
in 
    false 
end

end
