structure AST =
struct

  open HolKernel
  fun f() = let
    (* carriage return character on end of next line is deliberate *)
    val estr = "Unary Minus: expected argument to be an int \
               \(either \    \fixed width or unbounded)"
  in
    dest_var ``SUC : num -> num`` handle HOL_ERR _ => raise Fail estr
  end
end (* struct *)

(*
Local variables:
mn-delete-trailing-whitespace-p: nil
End:
*)
