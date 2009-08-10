structure holCheckLib :> holCheckLib =

struct

    open ksTools
    open holCheck
    open modelTools

    val mk_state = ksTools.mk_state
    val holCheck = holCheck.holCheck

end