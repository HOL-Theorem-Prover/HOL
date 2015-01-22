structure baseLib :> baseLib =
struct

open HolKernel baseTheory

fun do_base_thing n = n + term_size (concl baseTRUTH)

end
