structure AncestryData :> AncestryData =
struct

open Theory Lib Feedback
datatype 'd action = Visit of string | Apply of 'd list

type ('delta,'value) adata_info = {
  tag : string, initial_values : (string * 'value) list,
  apply_delta : 'delta -> 'value -> 'value
}

val ERR = mk_HOL_ERR "AncestryData"

fun smem s e = HOLset.member(s,e)
fun sadd e s = HOLset.add(s,e)

val tdebug = get_tracefn "Theory.debug"

fun DPRINT s = if tdebug() > 0 then print s else ()

fun ancestry parents {thyname} =
    ImplicitGraph.bfs parents String.compare (fn _ => sadd) thyname
                      (HOLset.empty String.compare)

type ('d,'v) info =
     {get_deltas : {thyname: string} -> 'd list,
      dblookup : {thyname : string} -> 'v option,
      apply_delta : 'd -> 'v -> 'v, tag : string,
      parents : {thyname : string} -> string list}

fun fpluck f [] = NONE
  | fpluck f (h::t) = case f h of
                          NONE => Option.map (fn (v,r) => (v,h::r)) (fpluck f t)
                        | SOME v => SOME ((h,v),t)

fun merge (info : ('d,'v) info) thys : 'v =
    let
      val _ = DPRINT ("Calling " ^ #tag info ^ ":merge[" ^
                      String.concatWith ", " thys ^ "]")
      val {parents,get_deltas,apply_delta,...} = info
      fun recurse (A, aset) worklist =
          case worklist of
              [] => A
            | Visit thy :: rest =>
              if smem aset thy then recurse (A, aset) rest
              else
                let
                  val ps0 = parents {thyname = thy}
                  val ps = List.filter (not o smem aset) ps0
                  val deltas = get_deltas {thyname = thy}
                in
                  recurse (A, sadd thy aset)
                          (map Visit ps @ (Apply deltas :: rest))
                end
            | Apply ds :: rest =>
              recurse (rev_itlist apply_delta ds A, aset) rest
    in
      case thys of
          [] => raise ERR "merge" "Empty ancestor list"
        | _ => (
          case fpluck (fn thy => #dblookup info {thyname=thy}) thys of
              NONE => raise ERR "merge"
                            ("None of [ " ^ String.concatWith ", " thys ^
                             "] has value for " ^ #tag info)
            | SOME ((h,v0),rest) =>
              let
                fun par_g s = #parents info {thyname = s}
              in
                recurse (v0, sadd h (ancestry par_g {thyname=h}))
                        (map Visit rest)
              end
        )
    end

fun parent_onload extras {thyname,data = data_opt} =
    let
      open ThyDataSexp
      val {tag,apply_delta_hook,delta_side_effects,apply_delta,get_deltas,
           value_table} =
          extras
    in
      if thyname = "min" then ()
      else
        let
          val v0 =
              case data_opt of
                  NONE =>
                  let
                    val ps = Theory.parents thyname
                    val _ = DPRINT (tag ^ ":onload(" ^ thyname ^
                                    ",NONE)\n with " ^
                                    "parents = [" ^
                                    String.concatWith ", " ps ^ "]\n")
                  in
                    !apply_delta_hook ps
                  end
                | SOME data => (
                  case list_decode string_decode data of
                      NONE => raise ERR "AncestryData"
                                    ("make("^tag^") got bad ancestor sexp")
                    | SOME sl =>
                      let
                        val _ = DPRINT (tag ^ ":onload(" ^ thyname ^
                                        ",\nSOME [" ^
                                        String.concatWith ", " sl ^ "])\n")
                      in
                        !apply_delta_hook sl
                      end
                )
          val uds = get_deltas {thyname = thyname}
          val _ = List.app delta_side_effects uds
          val v = rev_itlist apply_delta uds v0
        in
          Sref.update value_table (Symtab.update (thyname,v))
        end
    end



fun make {info : ('delta,'value)adata_info, get_deltas, delta_side_effects} =
    let
      open ThyDataSexp
      val {tag, apply_delta, initial_values, ...} = info
      val value_table =
          Sref.new (itlist Symtab.update initial_values Symtab.empty)
      fun valueDB {thyname} =
          Symtab.lookup (Sref.value value_table) thyname

      (* calculates merged values in the "onload" hook *)
      val apply_delta_hook =
          ref (fn (ps : string list) =>
                  raise Fail "AncestryData: calling default hook")
      val parent_extras =
          {tag = tag, apply_delta_hook = apply_delta_hook,
           delta_side_effects = delta_side_effects,
           apply_delta = apply_delta, get_deltas = get_deltas,
           value_table = value_table}

      val {export = parent_export,
           segment_data = parent_segment_data, ...} =
          ThyDataSexp.new {
            thydataty = tag, merge = fn {old,new} => new,
            load = parent_onload parent_extras, other_tds = fn (s,_) => SOME s
          }
      fun parents thyname =
          case parent_segment_data thyname of
              NONE => Theory.parents (#thyname thyname)
            | SOME t => valOf (list_decode string_decode t)
      val info = {get_deltas = get_deltas, tag = tag,
                  dblookup = valueDB,
                  apply_delta = apply_delta,
                  parents = parents}
      val _ = apply_delta_hook := merge info
      fun set_ancestry sl =
          let
            val _ = parent_export (List $ map String sl)
            val v = merge info sl
          in
            Sref.update value_table (Symtab.update (current_theory(), v));
            v
          end
    in
      {merge = merge info, DB = valueDB,
       parents = parents, set_parents = set_ancestry}
    end

fun gen_other_tds {tag,dec,enc,P} (t, thyevent) =
    case t of
        ThyDataSexp.List raw_ds =>
        let
          val (rawgds, rawbads) = List.partition ThyDataSexp.uptodate raw_ds
        in
          case ThyDataSexp.list_decode dec (ThyDataSexp.List rawgds) of
              SOME ds =>
              let
                val (gds, bads) = List.partition P ds
              in
                if null rawbads andalso null bads then NONE
                else SOME (ThyDataSexp.mk_list enc gds)
              end
            | NONE => raise ERR "gen_other_tds"
                            ("Bad encoding (1) for tag: "^tag)
        end
      | _ => raise ERR "gen_other_tds" ("Bad encoding (2) for tag: "^tag)

fun fullmake (arg as {adinfo : ('delta,'value)adata_info,...}) =
    let
      val {adinfo, sexps, globinfo, uptodate_delta} = arg
      val {dec,enc} = sexps
      val {apply_to_global,initial_value} = globinfo
      val {initial_values, tag, apply_delta, ...} = adinfo

      (* single global value *)
      val global_value_ref = Sref.new initial_value
      fun get_global_value () = Sref.value global_value_ref
      fun update_global_value f = Sref.update global_value_ref f

      (* table of values per theory *)
      val value_table =
          Sref.new (itlist Symtab.update initial_values Symtab.empty)
      fun valueDB {thyname} = Symtab.lookup (Sref.value value_table) thyname

      (* store deltas *)
      val {export = export_raw_delta, segment_data = get_raw_deltas,
           set = set_raw_deltas} =
          ThyDataSexp.new {thydataty = tag ^ ".deltas",
                           merge = ThyDataSexp.append_merge,
                           load = fn _ => (),
                           other_tds = gen_other_tds {tag=tag ^ ".deltas",
                                                      P = uptodate_delta,
                                                      enc = enc, dec = dec
                                                     }
                          }
      fun get_deltas {thyname} =
          case get_raw_deltas {thyname=thyname} of
              NONE => []
            | SOME d => (
              case ThyDataSexp.list_decode dec d of
                  SOME ds => ds
                | NONE => raise ERR "fullmake" "get_deltas: bad decode"
            )

      (* store parentage *)
      val apply_delta_hook =
          ref (fn (ps : string list) =>
                  raise Fail "AncestryData: calling default hook")
      fun delta_side_effects d =
          update_global_value (apply_to_global d)
      val parent_extras =
          {tag = tag, apply_delta_hook = apply_delta_hook,
           delta_side_effects = delta_side_effects,
           apply_delta = apply_delta, get_deltas = get_deltas,
           value_table = value_table}
      val {export = export_raw_parents, segment_data = get_raw_parents,
           set = set_raw_parents} =
          ThyDataSexp.new {thydataty = tag ^ ".parents",
                           merge = (fn {old,new} => new),
                           load = parent_onload parent_extras,
                           other_tds = (fn (t,_) => SOME t)}

      val info =
          {get_deltas = get_deltas,
           dblookup = raise Fail "Unimplemented",
           apply_delta = apply_delta,
           tag = tag,
           parents = raise Fail "Unimplemented"}
      fun set_ancestry sl =
          let
            open ThyDataSexp
            val _ = set_raw_deltas (List [])
            val _ = export_raw_parents (List $ map String sl)
            val v = merge info sl
          in
            Sref.update value_table (Symtab.update (current_theory(), v));
            v
          end
    in
      {merge = merge info, DB = valueDB,
       get_deltas = get_deltas,
       record_delta = raise Fail "Unimplemented",
       parents = parents,
       set_parents = set_ancestry,
       get_global_value = get_global_value,
       update_global_value = update_global_value}
    end


end (* struct *)
