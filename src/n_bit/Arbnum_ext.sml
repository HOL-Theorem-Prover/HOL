structure Arbnum_ext :> Arbnum_ext =
struct

local
  fun toHexChar n =
      str (if n < 10 then chr (ord #"0" + n)
                     else chr (ord #"A" + n - 10))
  open Arbnum
  val base = fromInt 16
in
  fun toHexString n =
    let val (q,r) = divmod(n, base)
        val s = toHexChar (toInt r)
  in
    if q = zero then s else (toHexString q)^s
  end
end

end
