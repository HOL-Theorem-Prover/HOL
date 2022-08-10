signature TexTokenMap =
sig

  val TeX_notation : {hol: string, TeX : string * int} -> unit
  val temp_TeX_notation : {hol: string, TeX : string * int} -> unit

  val the_map : unit ->
                (string,{thy : string, info : string * int})Binarymap.dict

end
