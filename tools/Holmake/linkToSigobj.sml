(*
Meant to achieve the effect of the following shell-script


--
for i in *.uo *.ui *.sig
do
  b=$(basename $i)
  if [ "$b" = "selftest.uo" -o "$b" = "selftest.ui" ]
  then
    :
  else
    ln -sf `pwd`/$i $(SIGOBJ)
  fi
done

for i in *.sig
do
  echo $(pwd)/$(basename $i .sig) >> $(SIGOBJ)/SRCFILES
done
--

As written this is not good enough because an empty match (of `*.sig`
say), will result in *.sig being written into SRCFILES and a bogus
link also being put into SIGOBJ.  In principle,

  shopt -s nullglob

fixes this, but our regression-worker shells don't seem to respect this.
Moreover, the above is racey in its updates to SRCFILES.

*)

structure linkToSigobj =
struct

infix ++
fun f1 ++ f2 = OS.Path.concat(f1,f2)

fun die fname e =
    (TextIO.output(
        TextIO.stdErr,
        fname ^ ": Exception raised: " ^
        General.exnMessage e);
     OS.Process.exit OS.Process.failure)

fun link_it {basename,fullpath} =
    LTSprimitives.primLink {
      from = fullpath,
      to = Systeml.HOLDIR ++ "sigobj" ++ basename
    } handle e => die ("link_it{" ^ fullpath ^ "}") e

fun isInteresting s =
    let val {base,ext} = OS.Path.splitBaseExt s
    in
      case ext of
          SOME s => base <> "selftest" andalso
                    (s = "sig" orelse s = "uo" orelse s = "ui")
        | NONE => false
    end

fun action {base,fakearcs} acc =
    let
      val d = OS.FileSys.getDir()
      val {base=b,ext} = OS.Path.splitBaseExt base
    in
      link_it {basename = base,fullpath = d ++ base};
      if ext = SOME "sig" then (d ++ b) :: acc else acc
    end

fun main() =
    let val dir = OS.FileSys.getDir()
        val toAdd =
            HFS_NameMunge.read_files_with_objs
              {dirname = dir}
              isInteresting
              action
              []
    in
      LTSprimitives.appendToSRCFILES toAdd handle e =>
      die ("appendToSRCFILES["^String.concatWith"," toAdd^"]") e
    end


end
