structure optionML :> optionML =
struct

  fun the (SOME x) = x

  fun is_none NONE = true | is_none (SOME _) = false
  fun is_some NONE = false | is_some (SOME _) = true

  fun option_join NONE = NONE
    | option_join (SOME x) = x

  fun option_map f (SOME x) = SOME (f x)
    | option_map f NONE     = NONE

val _ = app ConstMapML.insert
           [(optionSyntax.none_tm, ("Option","NONE")),
            (optionSyntax.some_tm, ("Option","SOME")),
            (optionSyntax.the_tm,  ("optionML","the")),
            (optionSyntax.is_none_tm, ("optionML","is_none")),
            (optionSyntax.is_some_tm, ("optionML","is_some")),
            (optionSyntax.option_join_tm, ("optionML","option_join")),
            (optionSyntax.option_map_tm, ("optionML","option_map"))];
end
