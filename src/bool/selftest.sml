(* tests that substitutions work, deferred until this point so that we get
   access to the parser (which is implicitly a test of the parser too) *)

open HolKernel Parse

fun substtest (M, x, N, result) = let
in
  print("Testing ["^term_to_string M^"/"^term_to_string x^"] ("^
        term_to_string N^") = "^term_to_string result^" ... ");
  if aconv (Term.subst[x |-> M] N) result then (print "OK\n"; true)
  else (print "FAILED!\n"; false)
end

val x = mk_var("x", Type.alpha)
val xfun = mk_var("x", Type.alpha --> Type.alpha)
val y = mk_var("y", Type.alpha)
val Id = mk_abs(x,x)
val Idy = mk_abs(y,y)

val tests = [(x,x,y,y),
             (x,y,y,x),
             (x,x,x,x),
             (y,x,Id,Id),
             (Id,xfun,xfun,Id),
             (x,y,Id,Idy),
             (y,x,``\y. y ^x : 'b``, ``\z. z ^y :'b``)]

val _ = Process.exit (if List.all substtest tests then Process.success
                      else Process.failure)
