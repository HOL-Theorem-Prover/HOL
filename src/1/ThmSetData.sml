structure ThmSetData :> ThmSetData =
struct

open DB Lib HolKernel

val ERR = mk_HOL_ERR "ThmSetData"

type data = LoadableThyData.t
datatype setdelta =
         ADD of string * thm   (* must be in qualified thy.name form *)
       | REMOVE of string (* could be anything *)

val added_thms = List.mapPartial (fn ADD (_, th) => SOME th | _ => NONE)

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

local
  open ThyDataSexp
in
val pp_sexp = pp_sexp Parse.pp_type Parse.pp_term Parse.pp_thm
fun sexp2string sexp = PP.pp_to_string (!Globals.linewidth) pp_sexp sexp
end;

datatype read_result = OK of setdelta | BAD_ADD of string

fun read ty sexp =
    let
      open ThyDataSexp
      fun decode1 sexp =
          case sexp of
              String nm =>
                (OK (ADD (nm,lookup_exn ty nm)) handle HOL_ERR _ => BAD_ADD nm)
            | List [String nm] => OK (REMOVE nm)
            | _ => raise ERR "read" ("Bad sexp for 1 update: "^sexp2string sexp)
    in
      case sexp of
          List deltas => map decode1 deltas
        | _ => raise ERR "read" ("Bad sexp for type "^ty^": "^sexp2string sexp)
    end

fun write_deltas ds =
    let
      open ThyDataSexp
      fun mapthis (ADD(nm,th)) = String nm
        | mapthis (REMOVE s) = List[String s]
      val sexps = map mapthis ds
    in
      List sexps
    end

fun write1 d = write_deltas [d]



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

type exportfns =
     { add : {thy : string, named_thms : (string * thm) list} -> unit,
       remove : {thy : string, removes : string list} -> unit}

type tabledata = ({thyname:string}->setdelta list) * exportfns

val data_map = ref (Symtab.empty : tabledata Symtab.table)

fun data_exportfns {settype = s} = Option.map #2 (Symtab.lookup (!data_map) s)

fun all_set_types () = Symtab.keys (!data_map)

fun theory_data {settype = key, thy} =
    case Symtab.lookup (!data_map) key of
      NONE => raise mk_HOL_ERR "ThmSetData" "theory_data"
                    ("No ThmSetData with name "^Lib.quote key)
    | SOME (sdf,_) => sdf {thyname=thy}

fun current_data {settype = s} =
    theory_data { settype = s, thy = current_theory() }

fun all_data {settype = s} =
    map (fn thy => (thy, theory_data {settype = s, thy = thy}))
        (current_theory() :: ancestry "-")


fun new_exporter {settype = name, efns = efns as {add, remove}} = let
  open TheoryDelta
  val dropBads =
      List.mapPartial
        (fn OK sd => SOME sd
        | BAD_ADD s => (HOL_WARNING "ThmSetData" "apply_delta"
                                    ("Bad add command, with name: "^s); NONE))
  fun apply_deltas thyname ds =
      let
        fun appthis (ADD (s,th)) =
               add {thy = thyname, named_thms = [(s, th)]}
          | appthis (REMOVE s) = remove {thy = thyname, removes =  [s]}
      in
        List.app appthis ds
      end
  fun loadfn {data,thyname} = apply_deltas thyname (dropBads (read name data))
  fun uptodate_thmdelta (ADD (s,th)) = uptodate_thm th
    | uptodate_thmdelta _ = true
  fun neqbinding s1 (ADD (s2,_)) =
         s1 <> s2 andalso current_theory () ^ "." ^ s1 <> s2
    | neqbinding _ _ = true
  fun toString (ADD (s,_)) = "ADD<" ^ s ^ ">"
    | toString (REMOVE s) = "REMOVE<" ^ s ^ ">"
  fun read_result_toString (OK sd) = toString sd
    | read_result_toString (BAD_ADD s) = "ADD<" ^ s ^ ">"
  fun check_result P (OK d) = P d
    | check_result _ (BAD_ADD s) = false
  fun revise_data P (deltas_sexp,td) =
      let
        val deltas = read name deltas_sexp
        val (ok,notok) = Lib.partition (check_result P) deltas
      in
        case notok of
            [] => NONE
          | _ => (HOL_WARNING
                      "ThmSetData" "revise_data"
                      ("\n  Theorems in set " ^ Lib.quote name ^
                       ":\n    " ^
                       String.concatWith ", " (map read_result_toString notok) ^
                       "\n  invalidated by " ^ TheoryDelta.toString td);
                  SOME (write_deltas (dropBads ok)))
      end

  fun hook (DelConstant _) = uptodate_thmdelta
    | hook (DelTypeOp _) = uptodate_thmdelta
    | hook (NewConstant _) = uptodate_thmdelta
    | hook (NewTypeOp _) = uptodate_thmdelta
    | hook (DelBinding s) = neqbinding s
    | hook (NewBinding(s,_)) = neqbinding s
    | hook _ = fn _ => true
  fun check_thydelta (arg as (sexp,td)) = revise_data (hook td) arg


  val {export = export_deltasexp, segment_data} =
      ThyDataSexp.new {merge = ThyDataSexp.append_merge, load = loadfn,
                       other_tds = check_thydelta, thydataty = name}
  fun opt2list (SOME x) = x | opt2list NONE = []
  fun segdata {thyname} =
      segment_data {thyname=thyname}
                   |> Option.map (dropBads o read name)
                   |> opt2list
  fun export p (* name * thm *) =
      let
      in
        add {thy = current_theory(), named_thms = [p]};
        export_deltasexp (write1 (ADD p))
      end

  fun onload thy = apply_deltas thy (segdata {thyname = thy})

  fun export_nameonly s =
      let val s = mk_store_name_safe s
      in
        export(s, lookup_exn name s)
      end
  fun delete s = let
    val data = write1 (REMOVE s)
  in
    remove {thy = current_theory(), removes = [s]};
    export_deltasexp data
  end

  fun store_attrfun {attrname,name,thm} = export (mk_store_name_safe name,thm)
  fun local_attrfun {attrname,name,thm} =
    add {thy = current_theory(), named_thms = [(name,thm)]}
in
  data_map := Symtab.update(name,(segdata, efns)) (!data_map);
  ThmAttribute.register_attribute (
    name, {storedf = store_attrfun, localf = local_attrfun}
  );
  List.app onload (ancestry "-");
  {export = export_nameonly, delete = delete}
end

end (* struct *)
