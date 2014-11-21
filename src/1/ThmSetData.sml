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

fun lookup ty s nm =
    SOME (uncurry DB.fetch (splitnm nm))
    handle HOL_ERR _ =>
           (Feedback.HOL_WARNING "ThmSetData" "lookup"
                                 ("Bad theorem name: \"" ^ nm ^ "\" from string \"" ^
                                  s ^ "\" and set-type \"" ^ ty ^ "\"");
            NONE)

fun read ty s =
  SOME (List.mapPartial
            (fn n => if n = "" then NONE
                     else
                       Option.map (fn r => (n,r)) (lookup ty s n))
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

(* ----------------------------------------------------------------------
    destfn: takes polymorphic theory data and turns it into the
            structured theorem data we want to use
    storefn: takes a theorem name and stores the associated theorem into
             the theory data.  Doesn't perform any associated update in
             the run-time memory
    exportfn: takes a string and a list of theorems and does something with
              them at runtime (adds them to a simpset, say).  The string is
              expected to be the name of the theory with which these
              theorems are associated.
   ---------------------------------------------------------------------- *)
type destfn = data -> (string * thm) list option
type storefn = string -> unit
type exportfn = (string -> thm list -> unit) option
val data_map = let
  open Binarymap
in
  ref (mkDict String.compare : (string,destfn * storefn * exportfn) dict)
end

fun data_storefn s = Option.map #2 (Binarymap.peek(!data_map,s))
fun data_exportfn s = Option.join (Option.map #3 (Binarymap.peek(!data_map,s)))

fun all_set_types () = Binarymap.foldr (fn (k,_,acc) => k::acc) [] (!data_map)

fun foldli f a l = let
  fun recurse a i l =
      case l of
        [] => a
      | h::t => recurse (f (i,h,a)) (i + 1) t
in
  recurse a 0 l
end

fun set_alist_merge(a1, a2) = let
  open Binarymap
  val emptyd = mkDict String.compare
  val offset = length a2
  val d1 = foldli (fn (i,(s,th),d) => insert(d,s,(i,th))) emptyd a1
  val d2 = foldli (fn (i,(s,th),d) => insert(d,s,(i+offset,th))) d1 a2
  val items0 = listItems d2
  val items = Listsort.sort (inv_img_cmp (#1 o #2) Int.compare) items0
in
  List.map (fn (s,(i,th)) => (s,th)) items
end

fun new ty = let
  val (mk,dest) = LoadableThyData.new {merge = set_alist_merge,
                                       read = read ty,
                                       write = writeset, thydataty = ty}
  fun foldthis (nm,set) =
      case lookup ty ("<internal>: "^nm) nm of
        SOME r => (nm, r) :: set
      | NONE => raise mk_HOL_ERR "ThmSetData" "new" ("Bad theorem name: "^nm)
  fun mk' slist =
      let val unencoded = foldl foldthis [] slist
      in
        (mk unencoded, unencoded)
      end
  fun store s = let
    val (data, _) = mk' [s]
  in
    LoadableThyData.write_data_update {thydataty = ty, data = data}
  end

  val _ = data_map := Binarymap.insert(!data_map,ty,(dest,store,NONE))
in
  (mk',dest)
end

fun theory_data {settype = key, thy} =
    case Binarymap.peek(!data_map, key) of
      NONE => raise mk_HOL_ERR "ThmSetData" "theory_data"
                    ("No ThmSetData with name "^Lib.quote key)
    | SOME (df,_,_) => let
        open LoadableThyData
      in
        case segment_data {thy = thy, thydataty = key} of
          NONE => []
        | SOME d => valOf (df d)
                    handle Option =>
                    raise mk_HOL_ERR "ThmSetData" "theory_data"
                          ("ThmSetData for name " ^ Lib.quote key ^
                           " doesn't decode")
      end

fun current_data s = theory_data { settype = s, thy = current_theory() }

fun all_data s = map (fn thy => (thy, theory_data {settype = s, thy = thy}))
                     (current_theory() :: ancestry "-")

fun new_exporter name addfn = let
  val (mk,dest) = new name
  open LoadableThyData TheoryDelta
  fun onload thyname =
      case segment_data {thy = thyname, thydataty = name} of
        NONE => ()
      | SOME d => let
          val thms = valOf (dest d)
        in
          addfn thyname (map #2 thms)
        end
  fun revise_data P td =
      case segment_data {thy = current_theory(), thydataty = name} of
        NONE => ()
      | SOME d => let
          val alist = valOf (dest d)
          val (ok,notok) = Lib.partition P alist
        in
          case notok of
            [] => ()
          | _ => (HOL_WARNING
                      "ThmSetData" "revise_data"
                      ("\n  Theorems in set " ^ Lib.quote name ^
                       ":\n    " ^ String.concatWith ", " (map #1 notok) ^
                       "\n  invalidated by " ^ TheoryDelta.toString td);
                  set_theory_data {thydataty = name,
                                   data = #1 (mk (map #1 ok))})
        end

  fun hook (TheoryLoaded s) = onload s
    | hook (td as DelConstant _) = revise_data (uptodate_thm o #2) td
    | hook (td as DelTypeOp _) = revise_data (uptodate_thm o #2) td
    | hook (td as NewConstant _) = revise_data (uptodate_thm o #2) td
    | hook (td as NewTypeOp _) = revise_data (uptodate_thm o #2) td
    | hook (td as DelBinding s) = revise_data (not o equal s o #1) td
    | hook _ = ()
  fun export s = let
    val (data, namedthms) = mk [s]
    val thms = map #2 namedthms
  in
    addfn (current_theory()) thms;
    write_data_update {thydataty = name, data = data}
  end
  val store = #2 (Binarymap.find(!data_map,name))
in
  data_map := Binarymap.insert(!data_map,name,(dest,store,SOME addfn));
  register_hook ("ThmSetData.onload." ^ name, hook);
  List.app onload (ancestry "-");
  {export = export, mk = mk, dest = dest}
end

fun new_storage_attribute s = let
in
  new_exporter s (fn _ => fn _ => ());
  Theory.adjoin_to_theory {
    sig_ps = NONE,
    struct_ps = SOME
      (fn pps =>
          PP.add_string pps
                 ("val _ = ThmSetData.new_exporter "^Lib.mlquote s^
                  " (fn _ => fn _ => ())\n"))
  }
end

fun store_attribute {attribute, thm_name} =
    case data_storefn attribute of
        NONE => raise mk_HOL_ERR "ThmSetData" "store_attribute"
                      ("Unknown attribute: "^attribute)
      | SOME f => f thm_name

end (* struct *)
