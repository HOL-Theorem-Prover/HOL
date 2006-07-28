signature MLstring =
sig

  exception stringerror of int * string
  val scanMLstring : string -> string

end
