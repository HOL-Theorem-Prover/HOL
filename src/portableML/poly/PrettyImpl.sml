structure PrettyImpl =
struct

  datatype pretty = datatype PolyML.pretty
  val prettyPrint = PolyML.prettyPrint

end
