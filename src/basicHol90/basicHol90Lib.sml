structure basicHol90Lib =
struct
  open boolTheory Drule Conv Tactical Tactic Rewrite
       Resolve Thm_cont Type_def_support Prim_rec;

  local open TypeBase Defn0 in end;

end;
