structure Symbolic :> Symbolic =
struct

val symb_map = [("Type",         "-->", "arrow"),
                ("Lib",          "|->", "maplet"),
                ("Lib",          "##",  "hash2"),
                ("bossLib",      "&&",  "amper2"),
                ("BasicProvers", "&&",  "amper2"),
                ("simpLib",      "++",  "plus2"),
                ("Parse",        "--",  "minus2"),
                ("Parse",        "==",  "equal2")];

fun unsymb "Type.-->"        = "Type.arrow"
  | unsymb "Lib.|->"         = "Lib.maplet"
  | unsymb "Lib.\\#\\#"      = "Lib.hash2"
  | unsymb "Lib.##"          = "Lib.hash2"
  | unsymb "bossLib.&&"      = "bossLib.amper2"
  | unsymb "BasicProvers.&&" = "BasicProvers.amper2"
  | unsymb "simpLib.++"      = "simpLib.plus2"
  | unsymb "bossLib.++"      = "bossLib.plus2"
  | unsymb "Parse.--"        = "Parse.minus2"
  | unsymb "Parse.=="        = "Parse.equal2"
  | unsymb other             = other;

fun tosymb "Type.arrow"          = "Type.-->"
  | tosymb "Lib.maplet"          = "Lib.|->" 
  | tosymb "Lib.hash2"           = "Lib.##"
  | tosymb "bossLib.amper2"      = "bossLib.&&"
  | tosymb "BasicProvers.amper2" = "BasicProvers.&&"
  | tosymb "simpLib.plus2"       = "simpLib.++"
  | tosymb "Parse.minus2"        = "Parse.--"
  | tosymb "Parse.equal2"        = "Parse.=="
  | tosymb other                 = other;

end
