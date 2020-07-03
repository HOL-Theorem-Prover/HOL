structure holmake_holpathdb =
struct

local
  val exts = holpathdb.search_for_extensions ReadHMF.find_includes
                                             [OS.FileSys.getDir()]
in
  val _ = List.app holpathdb.extend_db exts
end

end
