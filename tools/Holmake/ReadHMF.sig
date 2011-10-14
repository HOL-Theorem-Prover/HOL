signature ReadHMF =
sig

  type env = Holmake_types.env
  type ruledb = Holmake_types.ruledb
  val read : string -> env -> env * ruledb * string option

end;
