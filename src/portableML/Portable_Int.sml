structure Portable_Int =
    struct
        open Int
        exception Div = General.Div
        exception Mod = General.Div
    end
