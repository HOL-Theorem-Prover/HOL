structure HM_TheoryDat :> HM_TheoryDat =
struct

(* Cachekey ancestry discovery retains its conservative failure fallback.
   Cache acceptance uses TheoryDat.validate directly instead. *)
fun extract_parents dat_path =
    case TheoryDat.read_parents dat_path of
        TheoryDat.Success ps => map (fn {thy, hash} => (thy, hash)) ps
      | TheoryDat.Failure _ => []

fun find_parent_dat search_dirs thy =
    let
      val basename = thy ^ "Theory"
      val datname = basename ^ ".dat"
      fun access p = OS.FileSys.access (p, [OS.FileSys.A_READ])
                     handle _ => false
      fun in_dir d =
          let val munged = OS.Path.concat
                             (d, OS.Path.concat
                                   (HFS_NameMunge.HOLOBJDIR, datname))
              val plain = OS.Path.concat (d, datname)
          in
            if access munged then SOME munged
            else if access plain then SOME plain
            else NONE
          end
      fun first f [] = NONE
        | first f (x :: xs) =
            case f x of SOME y => SOME y | NONE => first f xs
      val sigobj = OS.Path.concat (Systeml.HOLDIR, "sigobj")
      val sigobj_uo = OS.Path.concat (sigobj, basename ^ ".uo")
      val sigobj_dat = OS.Path.concat (sigobj, datname)
    in
      case first in_dir search_dirs of
          SOME p => SOME p
        | NONE =>
          if access sigobj_dat then SOME sigobj_dat
          else if access sigobj_uo then
            let val real_uo = OS.FileSys.realPath sigobj_uo
                val real_dir = OS.Path.dir real_uo
                val candidate = OS.Path.concat (real_dir, datname)
            in
              if access candidate then SOME candidate else NONE
            end handle OS.SysErr _ => NONE
          else NONE
    end

end
