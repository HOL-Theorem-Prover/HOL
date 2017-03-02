use "mlton-srcs/Binarymap.sml";
use "mlton-srcs/Listsort.sml";
use "comparelogs.sml";

val _ = PolyML.shareCommonData main;
val _ = PolyML.export ("comparelogs", main);
