structure holpathdb :> holpathdb =
struct

val holpath_db =
    ref (Binarymap.mkDict String.compare : (string,string) Binarymap.dict)

fun lookup_holpath {vname = s} = Binarymap.peek(!holpath_db, s)

fun reverse_lookup {path} =
  let
    fun split vnm p0 p =
      "$(" ^ vnm ^ ")" ^ String.extract(p, size p0, NONE)
    fun foldthis (vnm, p, acc) =
      if String.isPrefix p path then
        case acc of
            NONE => SOME (size p, split vnm p path)
          | SOME (sz', p') => if size p > sz' then
                                SOME (size p, split vnm p path)
                              else acc
      else acc
  in
    case Binarymap.foldl foldthis NONE (!holpath_db) of
        NONE => path
      | SOME (_, p) => p
  end

fun extend_db {vname, path} =
  holpath_db := Binarymap.insert(!holpath_db, vname, path)

fun subst_pathvars modPath =
  let
    fun die s = (TextIO.output(TextIO.stdErr, "WARNING: " ^ s ^ "\n"); modPath)
  in
    if size modPath > 0 andalso String.sub(modPath, 0) = #"$" then
      if size modPath < 2 orelse String.sub(modPath, 1) <> #"(" then
        die ("Bad occurrence of $ in mod-path "^modPath)
      else
        let
          val (varname, rest) =
              Substring.position ")" (Substring.extract(modPath, 2, NONE))
          val varname = Substring.string varname
        in
          if Substring.size rest = 0 then
            die ("No matching r-paren in "^modPath)
          else
            let
              val rest = Substring.string
                           (Substring.dropl (fn c => c = #"/")
                                            (Substring.slice(rest,1,NONE)))
            in
              case lookup_holpath {vname = varname} of
                  NONE => die ("No HOL path for variable "^varname^" in " ^
                               modPath)
                | SOME p => OS.Path.concat(p,rest)
            end
        end
    else modPath
  end

end (* struct *)
