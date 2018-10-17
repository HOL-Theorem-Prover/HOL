structure Parmap :> Parmap =
struct

  open Future
  fun parmap f l = Par_List.map f l

  fun chunking_parmap {ratio,mincsz} f l =
    let
      val _ = mincsz >= 1 orelse raise Fail "chunking_parmap: mincsz < 1"
      val _ = ratio > 0 orelse raise Fail "chunking_parmap: ratio <= 0"
      val csz = length l div (ratio * Multithreading.max_threads())
    in
      if csz < mincsz then parmap f l
      else
        let
          val inp = Portable.chunk csz l
        in
          List.concat (parmap (List.map f) inp)
        end
    end


end;
