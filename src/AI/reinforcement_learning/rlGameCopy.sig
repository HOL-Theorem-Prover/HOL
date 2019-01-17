signature rlGameCopy =
sig

  include Abbrev

  type pos = int list

  datatype board =
  ScBoard of (term * (term * pos)) |
  LrBoard of (term * (term * pos)) |
  SucBoard of (term * (term * pos)) |
  AddBoard of (term * (term * pos)) |
  FailBoard

  datatype sitclass = ScClass | LrClass | SucClass | AddClass

  datatype move =
    Stop | Cont |
    Left | Right |
    Sz | Sal | Sar | Sss |
    Asa | Asl | Asr | Aac | Aasl | Aasr

  type sittools = 
  {
  class_of_sit: board psMCTS.sit -> sitclass,
  mk_startsit: term -> board psMCTS.sit,
  movel_in_sit: sitclass -> move list,
  nntm_of_sit: board psMCTS.sit -> term, 
  sitclassl: sitclass list
  }

  val sittools : sittools

  val rulespec : 
    (board psMCTS.sit -> psMCTS.status) * 
    (move -> board psMCTS.sit -> board psMCTS.sit)

end
