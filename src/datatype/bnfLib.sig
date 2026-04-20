signature bnfLib =
sig

include Abbrev
val specToFunctor : bnfBase.bnftor -> hol_type
val functorToMapAndSet : bnfBase.t -> hol_type ->
                         term * term * thm bnfBase_dtype.info HOLset.set

end
