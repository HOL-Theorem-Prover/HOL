signature DataSize =
sig
  include Abbrev

  val define_size : {induction:thm, recursion:thm}
                        -> TypeBasePure.typeBase
                        -> {def : thm,
                            const_tyopl : (term * (string*string)) list} option

end
