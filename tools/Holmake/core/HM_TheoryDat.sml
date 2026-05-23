structure HM_TheoryDat :> HM_TheoryDat =
struct

fun extract_parents dat_path =
    let
      val ins = TextIO.openIn dat_path
      val content = TextIO.inputAll ins
      val _ = TextIO.closeIn ins
      val full = Substring.full content
      val (_, at_theory) = Substring.position "(theory" full
    in
      if Substring.size at_theory < 7 then []
      else
        let
          val after_theory =
              Substring.dropl Char.isSpace (Substring.triml 7 at_theory)
          val (header, _) = Substring.position "(core-data" after_theory
          fun loop ss acc =
              let val (_, rest) = Substring.position "(\"" ss
              in
                if Substring.size rest < 2 then List.rev acc
                else
                  let
                    val after_open = Substring.triml 2 rest
                    val (xss, ass) = Substring.position "\"" after_open
                  in
                    if Substring.size ass < 1 then List.rev acc
                    else
                      let val ass1 = Substring.triml 1 ass
                      in
                        if Substring.isPrefix " . \"" ass1 then
                          let
                            val ass2 = Substring.triml 4 ass1
                            val (yss, ass3) = Substring.position "\"" ass2
                          in
                            if Substring.size ass3 >= 1 then
                              loop (Substring.triml 1 ass3)
                                   ((Substring.string xss,
                                     Substring.string yss) :: acc)
                            else List.rev acc
                          end
                        else loop ass1 acc
                      end
                  end
              end
        in loop header [] end
    end
    handle _ => []

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
