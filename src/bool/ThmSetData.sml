structure ThmSetData :> ThmSetData =
struct

open DB Lib HolKernel

type data = LoadableThyData.t

fun splitnm nm = let
  val comps = String.fields (equal #".") nm
in
  case comps of
    (thy::nm::_) => (thy, nm)
  | [name] => (current_theory(), name)
  | [] => raise Fail "String.fields returns empty list??"
end

fun lookup nm = uncurry DB.fetch (splitnm nm)

fun read s =
  SOME (map (fn n => (n, lookup n)) (String.fields Char.isSpace s))
  handle HOL_ERR _ => NONE


fun write slist = String.concatWith " " slist

fun writeset set = let
  fun foldthis ((nm,_), acc) = let
    val (thy,nm) = splitnm nm
  in
    (thy^"."^nm)::acc
  end
  val list = List.foldr foldthis [] set
in
  String.concatWith " " list
end

fun new s = let
  val (mk,dest) = LoadableThyData.new {merge = op@, read = read,
                                       write = writeset, thydataty = s}
  fun foldthis (nm,set) = (nm, lookup nm) :: set
  fun mk' slist = let val unencoded = foldl foldthis [] slist
                  in
                    (mk unencoded, unencoded)
                  end
in
  (mk',dest)
end

fun new_exporter name addfn = let
  val (mk,dest) = new name
  open LoadableThyData
  fun onload thyname =
    case segment_data {thy = thyname, thydataty = name} of
      NONE => ()
    | SOME d => let
        val thms = valOf (dest d)
      in
        addfn (map #2 thms)
      end
  fun export s = let
    val (data, namedthms) = mk [s]
    val thms = map #2 namedthms
  in
    addfn thms;
    write_data_update {thydataty = name, data = data}
  end
in
  register_onload onload;
  List.app onload (ancestry "-");
  {export = export, mk = mk, dest = dest}
end


end (* struct *)
