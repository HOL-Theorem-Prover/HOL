structure listLib :> listLib =
struct

  local open rich_listTheory in end;
  open ListConv1
  open ListConv2

(*    val _ = Lib.cons_path (!Globals.HOLdir^"library/list/help/defs/") 
                           Globals.help_path;
    val _ = Lib.cons_path (!Globals.HOLdir^"library/list/help/entries/") 
                          Globals.help_path;
    val _ = Lib.cons_path (!Globals.HOLdir^"library/list/help/thms/") 
                          Globals.help_path;
*)
end;
