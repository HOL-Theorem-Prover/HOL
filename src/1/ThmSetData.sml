structure ThmSetData :> ThmSetData =
struct

open DB Lib HolKernel

val ERR = mk_HOL_ERR "ThmSetData"

type data = LoadableThyData.t
type thname = KernelSig.kernelname
val name_toString = KernelSig.name_toString
datatype setdelta =
         ADD of thname * thm
       | REMOVE of string (* could be anything *)
datatype raw_delta = rADD of thname | rREMOVE of string
val added_thms = List.mapPartial (fn ADD (_, th) => SOME th | _ => NONE)

fun toKName s =
   case String.fields (equal #".") s of
       [s0] => {Thy = current_theory(), Name = s}
     | [s1,s2] => {Thy = s1, Name = s2}
     | _ => raise mk_HOL_ERR "ThmSetData" "toKName" ("Malformed name: " ^ s)

fun lookup_exn {Thy,Name} = DB.fetch Thy Name
fun mk_add s =
    let val nm = toKName s in ADD(nm, lookup_exn nm) end
      handle e as HOL_ERR _ => raise wrap_exn "ThmSetData" "mk_add" e

local
  open ThyDataSexp
in
val pp_sexp = pp_sexp Parse.pp_type Parse.pp_term Parse.pp_thm
fun sexp2string sexp = PP.pp_to_string (!Globals.linewidth) pp_sexp sexp
end;

datatype read_result = OK of setdelta | BAD_ADD of thname

fun raw_read1 ty sexp =
    let
      open ThyDataSexp
    in
      case sexp of
          KName nm => SOME (rADD nm)
        | String nm => SOME (rREMOVE nm)
        | _ => NONE
    end

fun raw_write1 d =
    let
      open ThyDataSexp
    in
      case d of
          rADD knm => KName knm
        | rREMOVE s => String s
    end

fun cook (rADD nm) = ADD(nm, lookup_exn nm)
  | cook (rREMOVE s) = REMOVE s

fun read ty sexp =
    let
      open ThyDataSexp
      fun decode1 sexp =
          case sexp of
              KName nm =>
                (OK (ADD (nm,lookup_exn nm)) handle HOL_ERR _ => BAD_ADD nm)
            | String nm => OK (REMOVE nm)
            | _ => raise ERR "read" ("Bad sexp for 1 update: "^sexp2string sexp)
    in
      case sexp of
          List deltas => map decode1 deltas
        | _ => raise ERR "read" ("Bad sexp for type "^ty^": "^sexp2string sexp)
    end

fun write10 d =
    case d of
        ADD(knm,th) => ThyDataSexp.KName knm
      | REMOVE s => ThyDataSexp.String s

fun write_deltas ds = ThyDataSexp.List (map write10 ds)

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
     { add : {thy : string, named_thm : (thname * thm)} -> unit,
       remove : {thy : string, remove : string} -> unit}

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
        | BAD_ADD s => (
          HOL_WARNING "ThmSetData" "apply_delta"
                      ("Bad add command, with name: "^name_toString s); NONE))
  fun apply_deltas thyname ds =
      let
        fun appthis (ADD (s,th)) = add {thy = thyname, named_thm = (s, th)}
          | appthis (REMOVE s) = remove {thy = thyname, remove =  s}
      in
        List.app appthis ds
      end
  fun loadfn {thyname, data = data_opt} =
      case data_opt of
          NONE => ()
        | SOME data => apply_deltas thyname (dropBads (read name data))
  fun uptodate_thmdelta (ADD (s,th)) = uptodate_thm th
    | uptodate_thmdelta _ = true
  fun neqbinding s1 (ADD ({Thy,Name},_)) =
         s1 <> Name orelse current_theory () <> Thy
    | neqbinding _ _ = true
  fun toString (ADD (s,_)) = "ADD<" ^ name_toString s ^ ">"
    | toString (REMOVE s) = "REMOVE<" ^ s ^ ">"
  fun read_result_toString (OK sd) = toString sd
    | read_result_toString (BAD_ADD s) = "ADD<" ^ name_toString s ^ ">"
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


  val {export = export_deltasexp, segment_data, ...} =
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
        add {thy = current_theory(), named_thm = p};
        export_deltasexp (write1 (ADD p))
      end

  fun onload thy = apply_deltas thy (segdata {thyname = thy})

  fun export_nameonly s =
      let val thnm = toKName s
      in
        export(thnm, lookup_exn thnm)
      end
  fun delete s = let
    val data = write1 (REMOVE s)
  in
    remove {thy = current_theory(), remove = s};
    export_deltasexp data
  end

  fun store_attrfun {attrname,name,args,thm} =
      if null args then export (toKName name,thm)
      else raise ERR "store_attrfun"
                 ("Arguments not allowed for attribute " ^ attrname)
  fun local_attrfun {attrname,name,args,thm} =
      if null args then
        add {named_thm = ({Thy = current_theory(), Name = name},thm),
             thy = current_theory()}
      else raise ERR "local_attrfun"
                 ("Arguments not allowed for attribute " ^ attrname)
in
  data_map := Symtab.update(name,(segdata, efns)) (!data_map);
  ThmAttribute.register_attribute (
    name, {storedf = store_attrfun, localf = local_attrfun}
  );
  List.app onload (ancestry "-");
  {export = export_nameonly, delete = delete}
end

fun lift nm = {Thy = current_theory(), Name = nm}

fun mk_raw (ADD(nm,_)) = rADD nm
  | mk_raw (REMOVE s) = rREMOVE s

type 'value ops = {apply_to_global : setdelta -> 'value -> 'value,
                   thy_finaliser : ({thyname:string} -> setdelta list ->
                                    'value -> 'value) option,
                   uptodate_delta : setdelta -> bool, initial_value : 'value,
                   apply_delta : setdelta -> 'value -> 'value}
fun raw_uptodate (rADD{Thy,Name}) = can (DB.fetch Thy) Name
  | raw_uptodate _ = true

fun export_with_ancestry
      {settype,delta_ops:'value ops}:(setdelta,'value)AncestryData.fullresult =
    let
      val {apply_to_global, uptodate_delta, initial_value, apply_delta,
           thy_finaliser} =
          delta_ops
      fun raw_apply_delta d = apply_delta (cook d)
      fun raw_apply_global d = apply_to_global (cook d)
      fun mk_raw_finaliser f thy ds = f thy (map cook ds)
      val raw_finaliser = Option.map mk_raw_finaliser thy_finaliser
      val adinfo = {tag = settype, initial_values = [("min", initial_value)],
                    apply_delta = raw_apply_delta}
      val sexps = {dec = raw_read1 settype, enc = raw_write1}
      val globinfo = {apply_to_global = raw_apply_global,
                      thy_finaliser = raw_finaliser,
                      initial_value = initial_value}
      fun uptodate rd = raw_uptodate rd andalso uptodate_delta (cook rd)
      val fullresult =
          AncestryData.fullmake { adinfo = adinfo,
                                  uptodate_delta = uptodate,
                                  sexps = sexps, globinfo = globinfo}
      fun store_attrfun {attrname,name,thm,args} =
          if null args then
            let val d = rADD(lift name)
            in
              #record_delta fullresult d;
              #update_global_value fullresult (raw_apply_global d)
            end
          else raise ERR "store_attrfun"
                     ("Arguments not allowed for attribute " ^ attrname)
      fun local_attrfun {attrname,name,thm,args} =
          (* as this is local, the name is not going to be a valid binding,
             and "cooking" a raw ADD delta will just throw an exception *)
          if null args then
            #update_global_value fullresult(apply_to_global (ADD(lift name, thm)))
          else
            raise ERR "local_attrfun"
                  ("Arguments not allowed for attribute " ^ attrname)
      fun efn_add {thy,named_thm} =
          #update_global_value fullresult(raw_apply_global(rADD (#1 named_thm)))
      fun efn_remove {thy,remove} =
          #update_global_value fullresult (raw_apply_global (rREMOVE remove))
      val efns = {add = efn_add, remove = efn_remove}
      val get_fulldeltas = map cook o #get_deltas fullresult
    in
      data_map := Symtab.update(settype, (get_fulldeltas, efns)) (!data_map);
      ThmAttribute.register_attribute (
        settype, {storedf = store_attrfun, localf = local_attrfun}
      );
      {merge = #merge fullresult, DB = #DB fullresult,
       get_deltas = get_fulldeltas,
       record_delta = #record_delta fullresult o mk_raw,
       parents = #parents fullresult, set_parents = #set_parents fullresult,
       get_global_value = #get_global_value fullresult,
       update_global_value = #update_global_value fullresult
      }
    end


(* ----------------------------------------------------------------------
    Some simple instances
   ---------------------------------------------------------------------- *)

type simple_dictionary = (string,thm) Binarymap.dict
fun sdict_apply_delta delta (d : simple_dictionary) =
    case delta of
        ADD({Thy,Name}, th) => Binarymap.insert(d, Thy ^ "." ^ Name, th)
      | REMOVE n => #1 (Binarymap.remove(d, n)) handle NotFound => d
fun simple_dictionary_ops i =
    {apply_to_global = sdict_apply_delta, apply_delta = sdict_apply_delta,
     thy_finaliser = NONE, uptodate_delta = K true, initial_value = i}
fun export_simple_dictionary {settype,initial} =
    let
      val i =
          List.foldl (fn ((n,th), d) => Binarymap.insert(d, n, th))
                     (Binarymap.mkDict String.compare) initial
      val ops as {apply_delta,...} = simple_dictionary_ops i
      val res = export_with_ancestry {settype = settype, delta_ops = ops}
      val updgv = #update_global_value res
      fun temp_exclude s = updgv (apply_delta (REMOVE s))
      fun temp_export s = updgv (apply_delta (mk_add s))
      val getDB = #get_global_value res
    in
      {merge = #merge res, DB = #DB res,
       temp_exclude = temp_exclude,
       exclude = (fn s => (temp_exclude s; #record_delta res (REMOVE s))),
       temp_export = temp_export,
       export = (fn s => (temp_export s; #record_delta res (mk_add s))),
       getDB = getDB,
       get_thms = Binarymap.foldl (fn (n,th,A) => th::A) [] o getDB,
       temp_setDB = updgv o K}
    end

fun sdict_withflag_thms({getDB,temp_setDB}, thms) f x =
    let
      open Binarymap
      val (_, tdb) =
          List.foldl (fn (th,(n,db)) => (n + 1, insert(db, Int.toString n, th)))
                     (0, mkDict String.compare)
                     thms
    in
      Portable.genwith_flag({get=getDB,set=temp_setDB}, tdb) f x
    end

type alist = (string * thm) list
fun alist_rm n [] = []
  | alist_rm n ((kv as (m,_)) :: rest) =
    if m = n then rest else (kv :: alist_rm n rest)
fun assoc_cons (n, th) alist = (n,th) :: alist_rm n alist
fun alist_apply_delta delta (d : alist) =
    case delta of
        ADD({Thy,Name}, th) => assoc_cons (Thy ^ "." ^ Name, th) d
      | REMOVE n => alist_rm n d
fun alist_ops i =
    {apply_to_global = alist_apply_delta, apply_delta = alist_apply_delta,
     thy_finaliser = NONE, uptodate_delta = K true, initial_value = i}
fun export_alist {settype,initial} =
    let
      val ops as {apply_delta,...} = alist_ops initial
      val res = export_with_ancestry {settype = settype, delta_ops = ops}
      val updgv = #update_global_value res
      fun temp_exclude s = updgv (apply_delta (REMOVE s))
      fun temp_export s = updgv (apply_delta (mk_add s))
      val getDB = #get_global_value res
    in
      {merge = #merge res, DB = #DB res,
       temp_exclude = temp_exclude,
       exclude = (fn s => (temp_exclude s; #record_delta res (REMOVE s))),
       temp_export = temp_export,
       export = (fn s => (temp_export s; #record_delta res (mk_add s))),
       getDB = getDB,
       get_thms = List.foldr (fn ((_,th),A) => th::A) [] o getDB,
       temp_setDB = updgv o K}
    end

fun alist_withflag_thms({getDB,temp_setDB}, thms) f x =
    let
      open Binarymap
      val (_, tdb) =
          List.foldr (fn (th,(n,db)) => (n + 1, (Int.toString n, th)::db))
                     (0, []) thms
    in
      Portable.genwith_flag({get=getDB,set=temp_setDB}, tdb) f x
    end

fun list_apply_delta delta ( d : thm list) =
    case delta of
        ADD(_, th) => th :: d
      | REMOVE _ => raise mk_HOL_ERR "ThmSetData" "list_apply_delta"
                          "Can't REMOVE in list set"
fun list_ops i =
    {apply_to_global = list_apply_delta, apply_delta = list_apply_delta,
     thy_finaliser = NONE, uptodate_delta = K true, initial_value = i}
fun thm_eq th1 th2 = aconv (concl th1) (concl th2)
fun export_list {settype,initial} =
    let
      val ops as {apply_delta,...} = list_ops initial
      val res = export_with_ancestry {settype = settype, delta_ops = ops}
      val updgv = #update_global_value res
      fun temp_exclude th = updgv (fn ths => op_set_diff thm_eq ths [th])
      fun temp_export s = updgv (apply_delta (mk_add s))
      val getDB = #get_global_value res
    in
      {merge = #merge res, DB = #DB res,
       temp_exclude = temp_exclude,
       temp_export = temp_export,
       export = (fn s => (temp_export s; #record_delta res (mk_add s))),
       getDB = getDB,
       temp_setDB = updgv o K}
    end

end (* struct *)
