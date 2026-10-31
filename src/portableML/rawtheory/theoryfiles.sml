structure theoryfiles :> theoryfiles =
struct

infix |>
fun x |> f = f x

infix ++
val op++ = OS.Path.concat

type theory_locn_map = string list Symtab.table

(* ----------------------------------------------------------------------
    Depth-first, preorder
   ---------------------------------------------------------------------- *)
fun recurse_toDirs action A worklist =
    case worklist of
        [] => A
      | d::ds =>
        let
          val A' = action d A
          val ds' = Portable.listDir d
                                     |> map (fn f => d ++ f)
                                     |> List.filter OS.FileSys.isDir
        in
          recurse_toDirs action A' (ds' @ ds)
        end

fun find_theory_files_action dir A =
  let
    open OS.FileSys
    val objsdirname = HFS_NameMunge.objdir_for dir
  in
    if access (objsdirname, [A_READ, A_EXEC])
       andalso isDir objsdirname then
      let
        val thys =
          Portable.listDir objsdirname
          |> List.filter (String.isSuffix "Theory.dat")
        fun collect (thyfile, acc) =
          let
            val thydat = dir ++ thyfile
            val {base, ...} = OS.Path.splitBaseExt thyfile
            val thy_name =
              String.substring (base, 0, size base - 6)
          in
            Symtab.cons_list (thy_name, thydat) acc
          end
      in
        List.foldl collect A thys
      end
    else A
  end

end
