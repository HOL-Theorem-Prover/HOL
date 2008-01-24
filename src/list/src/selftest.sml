open HolKernel Parse boolLib
open ListConv1

fun test nm cmp pr f (x, expected) = let
  val _ = print (StringCvt.padRight #" " 20 nm)
  val _ = print (StringCvt.padRight #" " 40 (pr x))
  val result = f x
in
  if cmp(rhs (concl result),expected) = EQUAL andalso null (hyp result) then
    (print "OK\n"; true)
  else (print "FAILED\n"; false)
end

val _ =
    if List.all (test "FIRSTN_CONV" Term.compare term_to_string FIRSTN_CONV)
                [(``FIRSTN 3 [1;2;3;4;5]``, ``[1;2;3]``),
                 (``FIRSTN 4 [1;2;3;4]``, ``[1;2;3;4]``),
                 (``FIRSTN 0 [1;2]``, ``[] : num list``),
                 (``FIRSTN 0 [] : num list``, ``[] : num list``)]
       andalso
       List.all
           (test "BUTFIRSTN_CONV" Term.compare term_to_string BUTFIRSTN_CONV)
           [(``BUTFIRSTN 3 [1;2;3;4]``, ``[4]``),
            (``BUTFIRSTN 0 [1;2]``, ``[1;2]``),
            (``BUTFIRSTN 3 [1;2;3]``, ``[] : num list``),
            (``BUTFIRSTN 0 [] : num list``, ``[] : num list``)]
    then
      Process.exit Process.success
    else Process.exit Process.failure
