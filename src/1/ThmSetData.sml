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

fun lookup nm =
    SOME (uncurry DB.fetch (splitnm nm))
    handle HOL_ERR _ =>
           (Feedback.HOL_WARNING "ThmSetData" "lookup"
                                 ("Bad theorem name: " ^ nm);
            NONE)

fun read s =
  SOME (List.mapPartial
            (fn n => Option.map (fn r => (n,r)) (lookup n))
            (String.fields Char.isSpace s))
  handle HOL_ERR _ => NONE

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
  fun foldthis (nm,set) =
      case lookup nm of
        SOME r => (nm, r) :: set
      | NONE => raise mk_HOL_ERR "ThmSetData" "new" ("Bad theorem name: "^nm)
  fun mk' slist =
      let val unencoded = foldl foldthis [] slist
      in
        (mk unencoded, unencoded)
      end
in
  (mk',dest)
end

fun new_exporter name addfn = let
  val (mk,dest) = new name
  open LoadableThyData TheoryDelta
  fun onload thyname =
      case segment_data {thy = thyname, thydataty = name} of
        NONE => ()
      | SOME d => let
          val thms = valOf (dest d)
        in
          addfn (map #2 thms)
        end
  fun hook (TheoryLoaded s) = onload s
    | hook _ = ()
  fun export s = let
    val (data, namedthms) = mk [s]
    val thms = map #2 namedthms
  in
    addfn thms;
    write_data_update {thydataty = name, data = data}
  end
in
  register_hook ("ThmSetData.onload." ^ name, hook);
  List.app onload (ancestry "-");
  {export = export, mk = mk, dest = dest}
end


end (* struct *)
