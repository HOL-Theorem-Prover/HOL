structure HolmakeCacheFetch =
struct

fun upload _ _ _ _ (ofns : Holmake_tools.output_functions) = let
    val _ = #warn ofns "Holmake cache is not supported with mosml."
in
    false
end

fun fetch _ _ (ofns : Holmake_tools.output_functions) = let
    val _ = #warn ofns "Holmake cache is not supported with mosml."
in
    false
end

end
