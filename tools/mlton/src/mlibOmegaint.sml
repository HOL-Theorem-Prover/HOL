(* Copyright (c) Ken Friis Larsen, Joe Hurd *)

structure mlibOmegaint :> mlibOmegaint =
struct 

  structure I = IntInf; local open IntInf in end;
  structure M = MLton.IntInf;
  structure V = Vector; local open Vector in end;
  structure W = Word; local open Word in end;

  val zero = I.fromInt 0;
  val one = I.fromInt 1;
  val eq = op=;

  fun hash n = 
    case M.rep n of
      M.Small w => w
    | M.Big v   =>
        let val k = W.toIntX (V.foldli (fn (_,w,acc) => w + acc) 0w0 (v,1,NONE))
        in if V.sub (v,0) = 0w0 then k else ~k
        end;

  open I;
  open M;

end


