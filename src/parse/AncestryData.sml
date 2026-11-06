structure AncestryData :> AncestryData =
struct

open Theory Lib Feedback
datatype 'd action = Visit of string | Apply of 'd list

type ('delta,'value) adata_info = {
  tag : string, initial_values : (string * 'value) list,
  apply_delta : 'delta -> 'value -> 'value
}

val ERR = mk_HOL_ERR "AncestryData"

val tdebug = get_tracefn "Theory.debug"

fun DPRINT s = if tdebug() > 0 then print ("* " ^s^"\n") else ()

(* theory based topologically sorted ancestry *)
fun tts_ancestry s : string list =
    let val G = SymGraph.make (map (fn s => ((s,()), Theory.parents s))
                                   (ancestry s))
    in
      List.rev (SymGraph.topological_order G)
    end

fun smem s e = HOLset.member(s,e)
fun sadd e s = HOLset.add(s,e)

(* Each theory's ancestry, the theory included.  A loaded theory's parents
   never change, so its ancestry is computed once per tag and kept in a
   context slot.  The current theory's parents can still change, as can
   those of "-" (the fringe of the theory graph), so their ancestries, and
   those of theories whose parents name them, are computed afresh on each
   use. *)
type ancestor_memo = string HOLset.set Symtab.table

(* A parent list may name the theory itself (e.g., after set_parents
   [current_theory()]); that edge adds nothing to its ancestry *)
fun proper_parents parents thy =
    List.filter (fn p => p <> thy) (parents {thyname = thy})

fun ancestor_set (memo : ancestor_memo) thy ps =
    foldl (fn (p, s) => HOLset.union (s, valOf (Symtab.lookup memo p)))
          (HOLset.singleton String.compare thy) ps

(* Add thy and its ancestors to the memo, except those described above.
   "-" is not visited: the fringe can include a theory whose parents name
   "-" *)
fun extend_memo parents (thy, memo) =
    if Symtab.defined memo thy orelse thy = "-" then memo
    else
      let
        val ps = proper_parents parents thy
        val memo' = foldl (extend_memo parents) memo ps
      in
        if Thm.getCT() = SOME thy orelse
           not (List.all (Symtab.defined memo') ps)
        then memo'
        else Symtab.update (thy, ancestor_set memo' thy ps) memo'
      end

(* The ancestry of a theory not in the memo *)
fun fresh_ancestry (memo : ancestor_memo) parents thy =
    let
      fun visit (t, acc) =
          if smem acc t then acc
          else
            case Symtab.lookup memo t of
                SOME s => HOLset.union (acc, s)
              | NONE => foldl visit (sadd t acc) (parents {thyname = t})
    in
      visit (thy, HOLset.empty String.compare)
    end

(* A function giving the ancestry of each theory in thys and in their
   ancestries *)
fun ancestor_sets slot parents thys =
    let
      val result = ref Symtab.empty
      fun extend memo =
          let
            val memo' = foldl (extend_memo parents) memo thys
          in
            result := memo'; memo'
          end
      val _ = Context.Data.modify slot extend
      val memo = !result
    in
      fn thy =>
         case Symtab.lookup memo thy of
             SOME s => s
           | NONE => fresh_ancestry memo parents thy
    end

type ('d,'v) info =
     {get_deltas : {thyname: string} -> 'd list,
      dblookup : {thyname : string} -> 'v Susp.susp option,
      apply_delta : 'd -> 'v -> 'v, tag : string,
      parents : {thyname : string} -> string list,
      ancestors : ancestor_memo Context.Data.slot}

fun fpluck _ [] = NONE
  | fpluck f (h::t) = case f h of
                          NONE => Option.map (fn (v,r) => (v,h::r)) (fpluck f t)
                        | SOME v => SOME ((h,v),t)

(* What a merge of thys starts from: the value of the first theory listed
   that has one, its ancestry, and the other theories, less those that are
   ancestors of theories listed.  NONE when no such theory has a value. *)
fun merge_start (info : ('d,'v) info) thys =
    let
      val {parents,ancestors,...} = info
      val ancs = ancestor_sets ancestors parents thys
      (* drop the theories that are ancestors of others in the list *)
      fun redundant thy =
          List.exists (fn t => t <> thy andalso smem (ancs t) thy) thys
      val thys = List.filter (not o redundant) thys
    in
      case fpluck (fn thy => #dblookup info {thyname=thy}) thys of
          NONE => NONE
        | SOME ((h,v0),rest) => SOME (v0, ancs h, rest)
    end

(* Apply, to the starting value, the deltas of the other theories and of
   their ancestors, each theory once *)
fun merge_from (info : ('d,'v) info) (v0, aset0, rest) : 'v =
    let
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
      recurse (Susp.force v0, aset0) (map Visit rest)
    end

fun merge (info : ('d,'v) info) thys : 'v option =
    let
      val _ = DPRINT ("Calling " ^ #tag info ^ ":merge[" ^
                      String.concatWith ", " thys ^ "]")
    in
      Option.map (merge_from info) (merge_start info thys)
    end

(* A theory's value is computed when first read, unless the instance's
   merges have side effects (eager).  It is also computed at once when the
   theory's ancestry is not fixed (its parents lead to the current theory
   or to "-"), since it would then depend on when it is read. *)
fun now v = Susp.delay (fn () => v)

(* thy's ancestry is fixed when it is not the current theory and its parents
   are in the memo, as extend_memo would then add it *)
fun fixed_ancestry slot thy ps =
    let
      val memo = Context.Data.get slot (Context.snapshot())
    in
      Thm.getCT() <> SOME thy andalso
      List.all (fn p => p = thy orelse Symtab.defined memo p) ps
    end

fun parent_onload extras {thyname,data = data_opt} =
    let
      open ThyDataSexp
      val {tag,info,delta_side_effects,eager,value_table} = extras
      val {apply_delta,get_deltas,ancestors,...} = info
    in
      if thyname = "min" then ()
      else
        let
          val ps =
              case data_opt of
                  NONE =>
                  let
                    val ps = Theory.parents thyname
                    val _ = DPRINT (tag ^ ":onload(" ^ thyname ^
                                    ",NONE)\n with " ^
                                    "parents = [" ^
                                    String.concatWith ", " ps ^ "]\n")
                  in
                    ps
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
                        sl
                      end
                )
          val _ = DPRINT ("Calling " ^ tag ^ ":merge[" ^
                          String.concatWith ", " ps ^ "]")
          fun store v =
              Context.Data.modify value_table (Symtab.update (thyname,v))
        in
          case merge_start info ps of
              NONE => ()
            | SOME start =>
              if eager orelse not (fixed_ancestry ancestors thyname ps)
              then
                let
                  val v0 = merge_from info start
                  val uds = get_deltas {thyname = thyname}
                  val _ = delta_side_effects thyname uds
                in
                  store (now (rev_itlist apply_delta uds v0))
                end
              else
                let
                  val _ = delta_side_effects thyname
                                             (get_deltas {thyname = thyname})
                in
                  store (Susp.delay (fn () =>
                           rev_itlist apply_delta
                                      (get_deltas {thyname = thyname})
                                      (merge_from info start)))
                end
          end
    end

fun make {info : ('delta,'value)adata_info, get_deltas, delta_side_effects} =
    let
      open ThyDataSexp
      val {tag, apply_delta, initial_values, ...} = info
      val value_table : 'value Susp.susp Symtab.table Context.Data.slot =
          Context.Data.new
            {name = "ancestry." ^ tag ^ ".values",
             empty = itlist (fn (thy,v) => Symtab.update (thy, now v))
                            initial_values Symtab.empty,
             pp = fn _ => "<ancestry." ^ tag ^ ".values>"}
      fun dbsusp_of ctxt {thyname} =
          Symtab.lookup (Context.Data.get value_table ctxt) thyname
      fun dbsusp arg = dbsusp_of (Context.snapshot()) arg
      fun valueDB_of ctxt arg = Option.map Susp.force (dbsusp_of ctxt arg)
      fun valueDB arg = valueDB_of (Context.snapshot()) arg

      (* calculates merged values in the "onload" hook *)
      fun side_effects _ = List.app delta_side_effects
      val parent_segment_data_ref = ref (fn _ => NONE)
      fun parents thyname =
          case !parent_segment_data_ref thyname of
              NONE => Theory.parents (#thyname thyname)
            | SOME t => valOf (list_decode string_decode t)
      val ancestors : ancestor_memo Context.Data.slot =
          Context.Data.new
            {name = "ancestry." ^ tag ^ ".ancestors",
             empty = Symtab.empty,
             pp = fn _ => "<ancestry." ^ tag ^ ".ancestors>"}
      val info = {get_deltas = get_deltas, tag = tag,
                  dblookup = dbsusp,
                  apply_delta = apply_delta,
                  parents = parents, ancestors = ancestors}
      val parent_extras =
          {tag = tag, info = info, delta_side_effects = side_effects,
           eager = true, value_table = value_table}

      val {export = parent_export,
           segment_data = parent_segment_data, ...} =
          ThyDataSexp.new {
            thydataty = tag, merge = #new,
            load = parent_onload parent_extras, other_tds = fn (s,_) => SOME s
          }
      val _ = parent_segment_data_ref := parent_segment_data
      fun set_ancestry sl =
          let
            val _ = parent_export (List $ map String sl)
            val vopt = merge info sl
          in
            (case vopt of
                SOME v =>
                Context.Data.modify value_table
                                    (Symtab.update (current_theory(), now v))
              | NONE => ());
            vopt
          end
      fun onload s =
          parent_onload parent_extras {
            thyname = s, data = parent_segment_data {thyname = s}
          }
    in
      List.app onload (tts_ancestry "-");
      {merge = merge info, DB = valueDB, DB_of = valueDB_of,
       parents = parents, set_parents = set_ancestry}
    end

fun gen_other_tds {tag,dec,enc,P} = let
  val last_scan_epoch = ref []
  (* P is a retire-state predicate (kernel-side via retire_epoch, DB-side
     via DB.fetch_knm which only transitions on DelBinding).  When
     retire_epoch is unchanged and the event is retire_captured, no
     stored delta's uptodate-status has moved. *)
  fun scan t =
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
  in fn (t, thyevent) =>
        let val cur = [Type.type_epoch(), Term.term_epoch ()] in
          if TheoryDelta.retire_captured thyevent andalso !last_scan_epoch = cur
          then NONE
          else scan t before last_scan_epoch := cur
        end
  end

type ('delta,'value) fullresult =
     { merge : string list -> 'value option,
       DB : {thyname : string} -> 'value option,
       DB_of : Context.t -> {thyname : string} -> 'value option,
       get_deltas : {thyname : string} -> 'delta list,
       record_delta : 'delta -> unit,
       parents : {thyname : string} -> string list,
       set_parents : string list -> 'value option,
       get_global_value : unit -> 'value,
       get_global_value_of : Context.t -> 'value,
       update_global_value : ('value -> 'value) -> unit,
       update_global_value_of : ('value -> 'value) -> Context.t ->
                                Context.t }

fun gen_fullmake eager
                 {adinfo:('delta,'value)adata_info, sexps, globinfo,
                  uptodate_delta} =
    let
      open ThyDataSexp
      val {dec,enc} = sexps
      val {apply_to_global,initial_value,thy_finaliser} = globinfo
      val {initial_values, tag, apply_delta, ...} = adinfo

      (* single global value *)
      val global_slot : 'value Context.Data.slot =
          Context.Data.new
            {name = "ancestry." ^ tag ^ ".global",
             empty = initial_value,
             pp = fn _ => "<ancestry." ^ tag ^ ".global>"}
      fun get_global_value_of ctxt = Context.Data.get global_slot ctxt
      fun get_global_value () = get_global_value_of (Context.snapshot())
      val update_global_value = Context.Data.modify global_slot
      val update_global_value_of = Context.Data.update global_slot

      (* table of values per theory *)
      val value_table : 'value Susp.susp Symtab.table Context.Data.slot =
          Context.Data.new
            {name = "ancestry." ^ tag ^ ".values",
             empty = itlist (fn (thy,v) => Symtab.update (thy, now v))
                            initial_values Symtab.empty,
             pp = fn _ => "<ancestry." ^ tag ^ ".values>"}
      fun dbsusp_of ctxt {thyname} =
          Symtab.lookup (Context.Data.get value_table ctxt) thyname
      fun dbsusp arg = dbsusp_of (Context.snapshot()) arg
      fun valueDB_of ctxt arg = Option.map Susp.force (dbsusp_of ctxt arg)
      fun valueDB arg = valueDB_of (Context.snapshot()) arg

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
      fun delta_side_effects thyname ds =
          case thy_finaliser of
              NONE => List.app (update_global_value o apply_to_global) ds
            | SOME f => update_global_value (f {thyname=thyname} ds)
      val get_raw_parents_ref = ref (fn _ => NONE)
      fun get_parents {thyname} =
          case !get_raw_parents_ref {thyname=thyname} of
              NONE => Theory.parents thyname
            | SOME t => valOf (list_decode string_decode t)

      val ancestors : ancestor_memo Context.Data.slot =
          Context.Data.new
            {name = "ancestry." ^ tag ^ ".ancestors",
             empty = Symtab.empty,
             pp = fn _ => "<ancestry." ^ tag ^ ".ancestors>"}
      val info =
          {get_deltas = get_deltas, dblookup = dbsusp,
           apply_delta = apply_delta, tag = tag, parents = get_parents,
           ancestors = ancestors}
      val parent_extras =
          {tag = tag, info = info, delta_side_effects = delta_side_effects,
           eager = eager, value_table = value_table}
      val {export = export_raw_parents, segment_data = get_raw_parents, ...} =
          ThyDataSexp.new {thydataty = tag ^ ".parents",
                           merge = #new,
                           load = parent_onload parent_extras,
                           other_tds = (fn (t,_) => SOME t)}
      val _ = get_raw_parents_ref := get_raw_parents
      fun set_ancestry sl =
          let
            val _ = set_raw_deltas (List [])
            val _ = export_raw_parents (List $ map String sl)
            val vopt = merge info sl
          in
            case vopt of
                SOME v =>
                (Context.Data.modify value_table
                                     (Symtab.update (current_theory(), now v));
                 update_global_value (K v))
              | NONE => ();
            vopt
          end
      fun record_delta d = export_raw_delta (ThyDataSexp.List [enc d])
      fun onload s =
          parent_onload parent_extras {thyname = s,
                                       data = get_raw_parents {thyname = s}}
      val _ = List.app onload (tts_ancestry "-")
    in
      {merge = merge info, DB = valueDB, DB_of = valueDB_of,
       get_deltas = get_deltas,
       record_delta = record_delta,
       parents = get_parents,
       set_parents = set_ancestry,
       get_global_value = get_global_value,
       get_global_value_of = get_global_value_of,
       update_global_value = update_global_value,
       update_global_value_of = update_global_value_of}
    end

fun fullmake x = gen_fullmake true x
fun lazy_fullmake x = gen_fullmake false x

fun with_temp_value (fr:('delta,'value)fullresult) v =
    Portable.genwith_flag ({ get = #get_global_value fr,
                             set = #update_global_value fr o K }, v)


end; (* struct *)
