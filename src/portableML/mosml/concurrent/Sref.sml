structure Sref :> Sref =
struct

type 'a t = 'a ref

fun value s = !s
fun update s f = (s := f (!s))
fun gen_update s f =
  let val (v',a) = f (!s)
  in
    s := v';
    a
  end
fun new v = ref v

end
