structure mlibOmegaint :> mlibOmegaint =
struct 

  structure I = MLton.IntInf;
  structure V = Vector; local open Vector in end;
  structure W = Word; local open Word in end;

  val zero = I.fromInt 0;
  val one = I.fromInt 1;
  val eq = op=;

  fun hash n = 
    case I.rep n of
      I.Small w => w
    | I.Big v   =>
        let val k = W.toIntX (V.foldli (fn (_,w,acc) => w + acc) 0w0 (v,1,NONE))
        in if V.sub (v,0) = 0w0 then k else ~k
        end;

  open I;

end


