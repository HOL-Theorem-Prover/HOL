structure holCheckLib :> holCheckLib = 

struct

    open ksTools
    open holCheck 

    val mk_state = ksTools.mk_state
    val holCheck = holCheck.holCheck

end