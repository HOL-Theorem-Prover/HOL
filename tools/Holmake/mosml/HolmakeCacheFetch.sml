structure HolmakeCacheFetch =
struct

fun upload _ _ _ _ _ warn = let
    val _ = warn "Holmake cache is not supported with mosml."
in
    false
end

fun fetch _ _ _ warn = let
    val _ = warn "Holmake cache is not supported with mosml."
in
    false
end

end
