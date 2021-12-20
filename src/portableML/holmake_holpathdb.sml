structure holmake_holpathdb =
struct

(* This file is used in the Moscow ML Holmake process.  It is compiled
   into the execution of script builds so that scripts get
   executed in an holpathdb environment that has been appropriately updated.

   Note how it only has side effects.
*)

local
  val exts = holpathdb.search_for_extensions ReadHMF.find_includes
                                             [OS.FileSys.getDir()]
in
  val _ = List.app holpathdb.extend_db exts
end

end
