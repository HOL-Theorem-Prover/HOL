structure HolmakeCacheFetch =
struct

fun upload _ _ _ _ talk = let
    val _ = talk "Holmake cache is not supported with mosml."
in
    false
end

fun fetch _ _ talk = let
    val _ = talk "Holmake cache is not supported with mosml."
in
    false
end

end
