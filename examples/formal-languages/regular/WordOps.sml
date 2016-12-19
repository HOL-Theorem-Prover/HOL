structure WordOps = 
struct

type word = IntInf.int;

val allzero = IntInf.fromInt 0;
val allones = IntInf.notb allzero;

(*---------------------------------------------------------------------------*)
(* Clear top (all but rightmost width) bits in w                             *)
(*---------------------------------------------------------------------------*)

fun clear_top_bits width w = 
 let open IntInf
     val mask = notb(<<(allones,Word.fromInt(width)))
 in andb(w,mask)
 end

fun clear_bot_bits width w = 
 let open IntInf
 in ~>>(w,Word.fromInt width)
 end

fun sign_extend w width = 
 let open IntInf
 in if ~>>(w,Word.fromInt (width - 1)) = 1
  then (* signed *)
     orb(w,IntInf.<<(allones,Word.fromInt width))
  else w
 end

end
