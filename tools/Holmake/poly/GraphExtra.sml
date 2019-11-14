structure GraphExtra :> GraphExtra =
struct

open Holmake_tools
open hm_target
type t = {holheap : dep option}

fun extra_deps {holheap = SOME d} = [d]
  | extra_deps {holheap = NONE} = []

fun get_extra0 {master_dir,master_cline : HM_Cline.t, envlist} =
    case envlist "HOLHEAP" of
        [] =>
        if #poly_not_hol master_cline then NONE
        else (
          case #holstate master_cline of
              NONE => SOME (filestr_to_tgt
                              (fullPath[Systeml.HOLDIR, "bin",
                                        "hol.state"]))
            | SOME s =>
              let
                val fp = hmdir.extendp {base = master_dir, extension = s}
                val {dir,file} = OS.Path.splitDirFile (hmdir.toAbsPath fp)
              in
                SOME (mk(hmdir.fromPath{origin="", path = dir}, toFile file))
              end
        )
      | [s] => SOME (filestr_to_tgt s)
      | _ => die_with ("Can't interpret HOLHEAP spec. in " ^
                       OS.FileSys.getDir())

fun get_extra i = {holheap = get_extra0 i}

fun toString {holheap = SOME d} = "heap="^tgt_toString d
  | toString {holheap = NONE} = "heap=*"

fun canIgnore d {holheap=SOME d'} = hm_target.compare(d,d') = EQUAL
  | canIgnore d _ = false

end
