(** Stripped down from:
  * https://stackoverflow.com/questions/69118919/sml-syntax-error-replacing-let-with-raise
  *
  * Nice example because it shows how much better our error messages are
  * for beginners...
  *)
fun foo ((d, m, y) : int * int * int) : int option =
  let
    if m = 1 orelse m = 2 then y - 1
    else y
    val bar = f (d, m, y) * 100000
    + stuff
    + stuff
    bar - g (bar - 100000, things)
  in
    if bar div 100000 <= 30 then SOME bar
    else NONE
  end
