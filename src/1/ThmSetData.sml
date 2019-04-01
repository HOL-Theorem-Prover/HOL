structure ThmSetData :> ThmSetData =
struct

open DB Lib HolKernel

type data = LoadableThyData.t
datatype delta = ADD of string   (* must be in qualified thy.name form *)
               | REMOVE of string (* could be anything *)
datatype setdelta = Addition of string * Thm.thm
                  | RemovalInstruction of string

fun get_thm (Addition(_, th)) = SOME th
  | get_thm _ = NONE
val added_thms = List.mapPartial get_thm

fun splitnm nm = let
  val comps = String.fields (equal #".") nm
in
  case comps of
    [thy,nm] => (thy, nm)
  | _ => raise Fail ("ThmSetData.splitnm applied to " ^ nm)
end

fun mk_store_name_safe s =
   case String.fields (equal #".") s of
       [s0] => current_theory() ^ "." ^ s
     | [s1,s2] => s
     | _ => raise mk_HOL_ERR "ThmSetData" "mk_store_name_safe"
                  ("Malformed name: " ^ s)

fun lookup_exn ty nm = uncurry DB.fetch (splitnm nm)

fun lookup ty nm =
    SOME (lookup_exn ty nm)
    handle HOL_ERR _ =>
           (Feedback.HOL_WARNING "ThmSetData" "lookup"
                                 ("Bad theorem name: \"" ^ nm ^
                                  "\" for set-type \"" ^ ty ^ "\"");
            NONE)

fun read ty s =
    let
      (* in case of ADD, checks that it refers to a theorem *)
      val encoded_deltas = String.fields Char.isSpace s
      fun check_s ds =
          if ds = "" then NONE
          else
            case (String.sub(ds,0), String.extract(ds,1,NONE)) of
                (#"0",ds') => SOME (REMOVE ds')
              | (#"1",ds') => Option.map (fn th => ADD ds') (lookup ty ds')
              | _ => (Feedback.HOL_WARNING "ThmSetData" "read"
                                           ("Bad delta: " ^ ds);
                      NONE)
    in
      SOME (List.mapPartial check_s encoded_deltas)
    end

fun writeset set = let
  fun foldthis (d, acc) =
      case d of
          ADD nm => "1"^nm :: acc
        | REMOVE s => "0"^s :: acc
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
    exportfn: takes a string and a list of names and theorems and does
              something with them at runtime (adds them to a simpset,
              say). The string is expected to be the name of the
              theory with which these theorems are associated.
   ---------------------------------------------------------------------- *)

type destfn = data -> delta list option
type storefn = string -> unit
type exportfns =
     { add : {thy : string, named_thms : (string * thm) list} -> unit,
       remove : {thy : string, removes : string list} -> unit}
val data_map = let
  open Binarymap
in
  ref
    (mkDict String.compare : (string,destfn * storefn * exportfns option) dict)
end

fun data_storefn {settype = s} = Option.map #2 (Binarymap.peek(!data_map,s))
fun data_exportfns {settype = s} =
    Option.join (Option.map #3 (Binarymap.peek(!data_map,s)))

fun all_set_types () = Binarymap.foldr (fn (k,_,acc) => k::acc) [] (!data_map)

fun new ty = let
  val (mk,dest) = LoadableThyData.new {merge = op@,
                                       read = Lib.K (read ty), terms = Lib.K [],
                                       write = Lib.K writeset, thydataty = ty}
  fun foldthis (nm,set) =
      case lookup ty nm of
        SOME r => (nm, r) :: set
      | NONE => raise mk_HOL_ERR "ThmSetData" "new" ("Bad theorem name: "^nm)
  fun store s =
      LoadableThyData.write_data_update {
        thydataty = ty,
        data = mk [ADD (mk_store_name_safe s)]
      }

  val _ = data_map := Binarymap.insert(!data_map,ty,(dest,store,NONE))
in
  (mk,dest)
end

fun theory_data0 {settype = key, thy} =
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

fun theory_data r =
    let
      fun lift sty (ADD nm) = Addition(nm, lookup_exn sty nm)
        | lift _ (REMOVE i) = RemovalInstruction i
    in
      theory_data0 r |> map (lift (#settype r))
    end

fun current_data {settype = s} =
    theory_data { settype = s, thy = current_theory() }


fun all_data {settype = s} =
    map (fn thy => (thy, theory_data {settype = s, thy = thy}))
        (current_theory() :: ancestry "-")


fun new_exporter {settype = name, efns = efns as {add, remove}} = let
  val (mk,dest) = new name
  open LoadableThyData TheoryDelta
  fun onload thyname =
      case segment_data {thy = thyname, thydataty = name} of
        NONE => ()
      | SOME d => let
          val deltas = valOf (dest d)
          fun appthis (ADD s) =
                add {thy = thyname, named_thms = [(s, lookup_exn name s)]}
            | appthis (REMOVE s) = remove {thy = thyname, removes =  [s]}
        in
          List.app appthis deltas
        end
  fun uptodate_thmdelta (ADD s) =
        (uptodate_thm (valOf (lookup name s)) handle Option => false)
    | uptodate_thmdelta _ = true
  fun neqbinding s1 (ADD s2) =
         s1 <> s2 andalso current_theory () ^ "." ^ s1 <> s2
    | neqbinding _ _ = true
  fun toString (ADD s) = s | toString (REMOVE s) = s
  fun revise_data P td =
      case segment_data {thy = current_theory(), thydataty = name} of
        NONE => ()
      | SOME d => let
          val delta_list = valOf (dest d)
          val (ok,notok) = Lib.partition P delta_list
        in
          case notok of
            [] => ()
          | _ => (HOL_WARNING
                      "ThmSetData" "revise_data"
                      ("\n  Theorems in set " ^ Lib.quote name ^
                       ":\n    " ^ String.concatWith ", " (map toString notok) ^
                       "\n  invalidated by " ^ TheoryDelta.toString td);
                  set_theory_data {thydataty = name, data = mk ok})
        end

  fun hook (TheoryLoaded s) = onload s
    | hook (td as DelConstant _) = revise_data uptodate_thmdelta td
    | hook (td as DelTypeOp _) = revise_data uptodate_thmdelta td
    | hook (td as NewConstant _) = revise_data uptodate_thmdelta td
    | hook (td as NewTypeOp _) = revise_data uptodate_thmdelta td
    | hook (td as DelBinding s) = revise_data (neqbinding s) td
    | hook _ = ()
  val store = #2 (Binarymap.find(!data_map,name))
  fun export s = let
    val s = mk_store_name_safe s
    val data = mk [ADD s]
  in
    add {thy = current_theory(), named_thms = [(s, lookup_exn name s)]};
    write_data_update {thydataty = name, data = data}
  end
  fun delete s = let
    val data = mk [REMOVE s]
  in
    remove {thy = current_theory(), removes = [s]};
    write_data_update {thydataty = name, data = data}
  end
in
  data_map := Binarymap.insert(!data_map,name,(dest,store,SOME efns));
  register_hook ("ThmSetData.onload." ^ name, hook);
  List.app onload (ancestry "-");
  {export = export, delete = delete}
end

fun new_storage_attribute s = let
in
  new_exporter {settype = s,
                efns =  { add = fn _ => (), remove = fn _ => () }};
  Theory.adjoin_to_theory {
    sig_ps = NONE,
    struct_ps = SOME
      (fn _ =>
          PP.add_string
                 ("val _ = ThmSetData.new_exporter {settype = " ^
                  Lib.mlquote s ^ ", efns = " ^
                  "{ add = fn _ => (), remove = fn _ => ()}}\n"))
  }
end

fun store_attribute {attribute, thm_name} =
    case data_storefn {settype=attribute} of
        NONE => raise mk_HOL_ERR "ThmSetData" "store_attribute"
                      ("Unknown attribute: "^attribute)
      | SOME f => f thm_name

end (* struct *)
