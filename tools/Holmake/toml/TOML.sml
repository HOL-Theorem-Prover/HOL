structure TOML :> TOML =
struct

open TOMLvalue_dtype
type key = string list

fun oassoc [] _ = NONE
  | oassoc ((j:string,v) :: rest) k = if j = k then SOME v else oassoc rest k

fun lookupInValue v k =
    case k of
        [] => SOME v
      | s::rest =>
        case v of
            TABLE svs => lookupInTable svs k
          | _ => NONE
and lookupInTable svs k =
    case k of
        [] => SOME (TABLE svs)
      | s::rest =>
        case oassoc svs s of
            NONE => NONE
          | SOME v => lookupInValue v rest

fun fromString s = valOf (StringCvt.scanString parseTOML.scan s)

fun fromFile path =
    let val istrm = TextIO.openIn path
        val res = TextIO.scanStream parseTOML.scan istrm
                  handle e => (TextIO.closeIn istrm; raise e)
    in
      valOf res
    end

type dirmerged = (string,table) Binarymap.dict

fun dmFromFile p = let val tab = fromFile p
                   in
                     Binarymap.insert(Binarymap.mkDict String.compare,
                                      p,
                                      tab)
                   end

fun mergeDMs dm1 dm2 = raise Fail "Unimplemented"
fun lookupValueFromPath dm path k = raise Fail "Unimplemented"


end (* struct *)
