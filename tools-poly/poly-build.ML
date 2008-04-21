val _ = use "poly/poly-init.ML";
val _ = use "Holmake/Systeml.sig";
val _ = use "Holmake/Systeml.sml";
val _ = use "build.sml";
val _ = PolyML.shareCommonData build.main;
val _ = PolyML.export ("build", build.main);
