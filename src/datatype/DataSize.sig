signature DataSize =
sig
  include Abbrev

  val define_size : thm -> TypeBasePure.typeBase 
                        -> {def : thm, 
                            const_tyopl : (term * string)list} option
                  
end
