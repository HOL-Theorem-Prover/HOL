structure arithLib :> arithLib =
struct
  open arbint
  val << = String.<

  open Arith

  (* val _ = Lib.cons_path (!Globals.HOLdir^"library/arith/help/entries/") 
                        Globals.help_path;
  *)

end;
