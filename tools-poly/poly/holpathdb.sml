structure holpathdb :> holpathdb =
struct

val holpath_db =
    ref (Binarymap.mkDict String.compare : (string,string) Binarymap.dict)

fun lookup_holpath {vname = s} = Binarymap.peek(!holpath_db, s)

fun reverse_lookup {path} =
  let
    fun split vnm p0 p =
      "$(" ^ vnm ^ ")/" ^ String.extract(p, size p0 + 1, NONE)
    fun foldthis (vnm, p, acc) =
      if String.isPrefix (p^"/") path then
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

fun warn s = TextIO.output(TextIO.stdErr, "WARNING: " ^ s ^ "\n")

fun subst_pathvars modPath =
  let
    fun die s = (warn s; modPath)
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

infix ++
fun p1 ++ p2 = OS.Path.concat(p1,p2)

fun check_insert(m,k,v) =
  let
    val _ =
        case Binarymap.peek(m,k) of
            NONE => ()
          | SOME v' => if v' <> v then
                         warn((v ++ ".holpath") ^ " overrides value for "^
                              k ^ " from " ^ (v' ++ ".holpath"))
                       else ()
  in
    Binarymap.insert(m,k,v)
  end

fun readVName d m =
  let
    val hp = d ++ ".holpath"
    val istrm = TextIO.openIn hp
    val m' =
        case TextIO.inputLine istrm of
            NONE => (warn (hp ^ " is empty"); m)
          | SOME s =>
            let
              val sz = size s - 1
              val nm = if String.sub(s,sz) = #"\n" then
                         String.extract(s,0,SOME sz)
                       else s
            in
              check_insert(m,nm,d)
            end
  in
    TextIO.closeIn istrm;
    m'
  end handle IO.Io _ => m


fun search_for_extensions gen dlist =
  let
    fun recurse acc visited dlist =
      case dlist of
          [] => acc
        | d::ds =>
          let
            val acc' = readVName d acc
            val pd = OS.Path.getParent d
            val visited' = Binaryset.add(visited, d)
            val new_ds =
                List.filter (fn d => not (Binaryset.member(visited', d)))
                            (pd :: gen d)
            val dlist' = new_ds @ ds
          in
            recurse acc' visited' dlist'
          end
  in
    Binarymap.foldl (fn (vnm,p,acc) => {vname=vnm,path=p} :: acc)
                    []
                    (recurse (Binarymap.mkDict String.compare)
                             (Binaryset.empty String.compare)
                             dlist)
  end


end (* struct *)
