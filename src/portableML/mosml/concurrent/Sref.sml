structure Sref :> Sref =
struct

type 'a t = 'a ref

fun value s = !s
fun update s f = (s := f (!s))
fun new v = ref v

end
