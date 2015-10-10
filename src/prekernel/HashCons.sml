structure HashCons :> HashCons = struct

open Lib

val hashstring = CharVector.foldl (fn (c,h) => Word.fromInt(Char.ord c) + h * 0w31) 0w0

type 'a weakref = 'a option ref

fun wr_compare cmp (ref wr1, ref wr2) = option_compare cmp (wr1, wr2)

type 'a hconsed = { node: 'a, tag : int } ref

fun node (ref {node,...}) = node
fun tag (ref {tag,...}) = tag

fun hc_compare cmp (ref {node=n1,tag=t1},ref {node=n2,tag=t2}) =
  if t1 = t2 then EQUAL else cmp (n1, n2)

fun hc_tag_compare x = (inv_img_cmp (#tag o !) Int.compare) x

type 'a htable = 'a hconsed weakref HOLset.set PIntMap.t

val empty_table = PIntMap.empty
fun mk_next_tag() =
  let
    val tag = ref 0
    fun next_tag () = (!tag before tag := !tag + 1)
  in
    next_tag
  end

fun mk_hashconsed eq next_tag table hash cons args =
  let
    val hk = hash args
    fun mk_new() =
      let
        val nr = ref {tag = next_tag(), node = cons args}
        val wr = Weak.weak (SOME nr)
      in
        (wr,nr)
      end
    fun not_there() =
      let
        val (wr,nr) = mk_new()
      in
        (HOLset.singleton (wr_compare hc_tag_compare) wr, nr)
      end
    fun is_there set =
      let
        fun findP (ref (SOME (ref {node,...}))) = eq(node,cons args)
          | findP _ = false
      in
        case HOLset.find findP set of
          NONE =>
            let
              val (wr,nr) = mk_new()
              val set' = HOLset.add(set,wr)
            in
              (set',nr)
            end
        | SOME (ref (SOME nr)) => (set,nr)
        | SOME (ref NONE) => raise Fail "Weak reference disappeared during pattern match"
      end
    val (t, r) = PIntMap.addfu is_there (Word.toInt hk) not_there (!table)
  in
    table := t; r
  end

end
