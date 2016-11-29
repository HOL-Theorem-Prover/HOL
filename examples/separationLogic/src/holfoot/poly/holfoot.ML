use "corecl.ML";

fun main () = holfoot_run (false, fn x => Parse.print_with_style [PPBackEnd.FG PPBackEnd.OrangeRed] "File mode not supported in compressed version!\n");
