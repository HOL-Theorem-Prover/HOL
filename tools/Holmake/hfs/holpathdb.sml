structure holpathdb :> holpathdb =
struct

val empty_strset = Binaryset.empty String.compare
type dbrec = {mapf : (string,string) Binarymap.dict,
              dom : string Binaryset.set, rng : string Binaryset.set}
val holpath_db : dbrec ref =
    ref {mapf = Binarymap.mkDict String.compare, dom = empty_strset,
         rng = empty_strset}

fun fold f x = Binarymap.foldl (fn (k,v,A) => f {vname = k, path = v} A) x
                               (#mapf (!holpath_db))

fun lookup_holpath {vname = s} = Binarymap.peek(#mapf (!holpath_db), s)

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
    case Binarymap.foldl foldthis NONE (#mapf (!holpath_db)) of
        NONE => path
      | SOME (_, p) => p
  end

fun extend_db {vname, path} =
    let val {mapf,dom,rng} = !holpath_db
    in
      holpath_db := {mapf = Binarymap.insert(mapf, vname, path),
                     dom = Binaryset.add(dom, vname),
                     rng = Binaryset.add(rng, path)}
    end

fun db_vnames() = #dom (!holpath_db)
fun db_dirs() = #rng (!holpath_db)

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

fun read_whole_file{filename} =
    let
      val istrm = TextIO.openIn filename
      fun readit A =
          case TextIO.inputLine istrm of
              NONE => (TextIO.closeIn istrm; String.concat (List.rev A))
            | SOME s => readit (s::A)
    in
      readit []
    end

fun set_member s e = Binaryset.member(s,e)
fun files_upward_in_hierarchy gen_extras {diag} {filename, starter_dirs, skip} =
    let
      val {arcs = farcs, isAbs = fabs, vol} = OS.Path.fromString filename
      val _ = not fabs andalso length farcs = 1 andalso vol = "" orelse
              raise Fail "files_upward_in_hierarchy: bad filename"
      fun maybe_readfile d A =
          let
            val f = OS.Path.concat (d,filename)
          in
            if OS.FileSys.access(f,[OS.FileSys.A_READ]) then
              Binarymap.insert(A, d, read_whole_file{filename = f})
            else A
          end

      fun recurse A visited worklist =
          case worklist of
              [] => A
            | [] :: rest => recurse A visited rest
            | (d0::ds) :: rest =>
              let
                val d = OS.Path.mkCanonical d0
                val _ = diag (fn _ => "Visiting " ^ d)
                val A' = maybe_readfile d A
                val visited' = Binaryset.add(visited, d)
                val parent = OS.Path.getParent d
                val to_maybe_visit = parent :: gen_extras d
                val to_visit = List.filter (not o set_member visited)
                                           to_maybe_visit
              in
                recurse A' visited' (to_visit :: ds :: rest)
              end
    in
      recurse (Binarymap.mkDict String.compare) skip
              [List.filter (not o set_member skip) starter_dirs]
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

fun process_filecontents s =
  let
    val sz = size s - 1
    val nm = if String.sub(s,sz) = #"\n" then String.extract(s,0,SOME sz) else s
  in
    nm
  end


fun search_for_extensions gen {skip,starter_dirs = dlist} =
  let
    val dmap = files_upward_in_hierarchy gen {diag = fn _ => ()}
                 {filename = ".holpath", starter_dirs = dlist, skip = skip}
    fun foldthis (dstr,filecontents,(l,revmap)) =
        let
          val nm = process_filecontents filecontents
        in
          ({vname=nm,path=dstr}::l, check_insert(revmap,nm,dstr))
        end
  in
    #1 (Binarymap.foldl foldthis ([],Binarymap.mkDict String.compare) dmap)
  end


end (* struct *)
