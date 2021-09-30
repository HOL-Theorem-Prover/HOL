val origdir = OS.FileSys.getDir();
OS.FileSys.chDir "../tools-poly";
val _ = use "poly/poly-init.ML";
OS.FileSys.chDir origdir;
use "../tools/Holmake/hmcore.ML";
use "generateBuildSummary.sml";
val main = generateBuildSummary.main
