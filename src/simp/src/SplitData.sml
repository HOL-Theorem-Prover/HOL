structure SplitData :> SplitData =
struct

open HolKernel
structure LTD = Theory.LoadableThyData
val ERR = mk_HOL_ERR "SplitData"
val apiERR = mk_HOL_ERR "splitLib"
val tag = "splitLib.persistent.rules.v1"
val listener_name = "splitLib.persistence.onload"

datatype raw_delta = Add of KernelSig.kernelname | Remove of string
(* The serialized stream holds names only. Applying an ADD resolves and
   validates its theorem in the active DB; live/local state retains the
   same theorem values as the previous split implementation. *)

type registration =
  {reversed_segment : string -> raw_delta list,
   record : raw_delta -> unit,
   set_reversed : raw_delta list -> unit,
   get : Context.t -> thm Symtab.table,
   update : (thm Symtab.table -> thm Symtab.table) -> unit,
   validate : thm -> unit}
val registration_slot : registration option Context.Data.slot =
  Context.Data.new {name="splitLib.registration", empty=NONE,
                   pp=fn _ => "<splitLib.registration>"}
val rules_slot : thm Symtab.table Context.Data.slot =
  Context.Data.new {name="splitLib.rules", empty=Symtab.empty,
                   pp=fn _ => "<splitLib.rules>"}

(* The registration lives in the same Context as the attribute it
   installed, so a rewind removes both together. *)
fun active ctxt = Context.Data.get registration_slot ctxt

fun encode_delta (Add {Thy,Name}) =
      HOLsexp.List [HOLsexp.Symbol "add",
                    HOLsexp.String Thy, HOLsexp.String Name]
  | encode_delta (Remove key) =
      HOLsexp.List [HOLsexp.Symbol "remove", HOLsexp.String key]
fun decode_delta s =
  case HOLsexp.list_decode SOME s of
      SOME [HOLsexp.Symbol "add", HOLsexp.String thy, HOLsexp.String name] =>
        SOME (Add {Thy=thy,Name=name})
    | SOME [HOLsexp.Symbol "remove", HOLsexp.String key] => SOME (Remove key)
    | _ => NONE
(* Keep the newest delta first in memory so recording one delta is
   constant-time. The wire format and replay order are oldest first. *)
fun encode ds = HOLsexp.tagged_encode "split-rules-v1"
  (HOLsexp.list_encode encode_delta) (List.rev ds)
fun decode data = Option.map List.rev
  (HOLsexp.tagged_decode "split-rules-v1"
     (HOLsexp.list_decode decode_delta) data)

fun apply validate (Add name) db =
      let val th = DB.fetch_knm name
      in validate th; Symtab.update (KernelSig.name_toString name,th) db end
  | apply _ (Remove key) db = Symtab.delete_safe key db
fun replay (r : registration) thy =
  #update r (fn db => List.foldl
    (fn (d,db) => apply (#validate r) d db) db
    (List.rev (#reversed_segment r thy)))

(* The sole process-global closure captures only stable private slot
   handles. Every event selects all operations from the active context. *)
fun dispatch td =
  case active (Context.snapshot ()) of
      NONE => ()
    | SOME r =>
        case td of
            TheoryDelta.TheoryLoaded thy => replay r thy
          | _ =>
              let
                val ds = #reversed_segment r (Theory.current_theory ())
                (* Match AncestryData.gen_other_tds: only the recorded
                   stream is pruned; local/live rules are left alone.
                   REMOVE keys are never dropped or resolved again. *)
                fun current (Add name) = can DB.fetch_knm name
                  | current (Remove _) = true
              in
                if List.all current ds then ()
                else #set_reversed r (List.filter current ds)
              end

fun listener () = List.find (fn (n,_) => n = listener_name)
  (Listener.listeners Theory.delta_hook)
fun check_listener () =
  case listener () of
      NONE => ()
    | SOME (_,f) =>
        if Portable.pointer_eq (f,dispatch) then ()
        else raise ERR "initialize" ("Foreign listener: " ^ listener_name)

(* Explicit initialization can repair a removed dispatcher, but must never
   replace a foreign function under the private listener name. *)
fun ensure_listener () =
  case listener () of
      NONE => (Theory.register_hook (listener_name,dispatch); true)
    | SOME _ => (check_listener (); false)

(* Same ancestor order as ordinary AncestryData initialization, with each
   node visited once. On later TheoryLoaded events only that node's deltas
   are replayed, including on repeated notifications. *)
fun ancestors () =
  List.rev (SymGraph.topological_order
    (SymGraph.make (map (fn s => ((s,()),Theory.parents s))
                        (Theory.ancestry "-"))))

fun initialize {validate} =
  let
    val entry = Context.snapshot ()
    fun conflict () = raise apiERR "enable_split_attribute"
      "settype or attribute split already exists"
    fun preflight () =
      if ThmAttribute.is_attribute "split" orelse
         Option.isSome (ThmSetData.data_exportfns {settype="split"}) orelse
         List.exists (equal "split") (ThmSetData.all_set_types ()) orelse
         List.exists (fn {abbrev,...} => abbrev = "split")
           (ThmAttribute.current_abbreviations ()) orelse
         not (null (#reserved (ThmAttribute.extract_attributes "rule[split]")))
      then conflict () else check_listener ()
    val installed = ref false
    fun allocate () =
      let
        val (to_data,from_data) = LTD.new
          {thydataty=tag, pp=K "<split rules v1>",
           merge=fn (older,newer) => newer @ older,
           terms=K [], strings=K [], read=K decode, write=K encode}
        fun reversed_segment thy =
          case LTD.segment_data {thy=thy,thydataty=tag} of
              NONE => []
            | SOME data =>
                (case from_data data of
                     SOME ds => ds
                   | NONE => raise ERR "theory_data"
                       "Foreign split data witness")
        fun record d =
          LTD.write_data_update {thydataty=tag,data=to_data [d]}
        fun set_reversed ds =
          LTD.set_theory_data {thydataty=tag,data=to_data ds}
        val update = Context.Data.modify rules_slot
        fun handler stored {name,attrname,args,thm} =
          let
            val ctxt = Context.snapshot ()
            val _ = if Context.is_pinned () then
              raise ERR "attribute" "cannot update in a pinned context"
              else ()
            val current = case active ctxt of SOME r => r
              | NONE => raise ERR "attribute"
                  "persistent split registration not enabled"
            val _ = if null args then () else
              raise ERR "attribute"
                ("Arguments not allowed for attribute " ^ attrname)
            val knm = {Thy=Theory.current_theory (),Name=name}
            val value = if stored then DB.fetch_knm knm else thm
            val _ = #validate current value
          in
            if stored then #record current (Add knm) else ();
            #update current (Symtab.update (KernelSig.name_toString knm,value))
          end
        val attribute = {storedf=handler true,localf=handler false}
        val r = {reversed_segment=reversed_segment, record=record,
                 set_reversed=set_reversed,
                 get=Context.Data.get rules_slot,
                 update=update,validate=validate}
      in
        ThmAttribute.register_attribute ("split",attribute);
        Context.Data.write rules_slot Symtab.empty;
        Context.Data.write registration_slot (SOME r);
        installed := ensure_listener ();
        List.app (replay r) (ancestors ())
      end
  in
    if Context.is_pinned () then raise apiERR "enable_split_attribute"
      "cannot initialize in a pinned context"
    else case active entry of
        SOME _ => ignore (ensure_listener ())
      | NONE =>
          (preflight ();
           allocate () handle e =>
             (Context.restore entry;
              if !installed then
                ignore
                  (Listener.remove_listener Theory.delta_hook listener_name)
              else ();
              raise e))
  end

fun exclude name =
  let val ctxt = Context.snapshot ()
  in
    if Context.is_pinned () then raise apiERR "exclude_split"
      "cannot retract in a pinned context"
    else case active ctxt of
        NONE => raise apiERR "exclude_split"
          "persistent split registration not enabled"
      | SOME r =>
          let val key = KernelSig.name_toString (ThmSetData.toKName name)
          in
            #record r (Remove key);
            #update r (Symtab.delete_safe key)
          end
  end

fun named_rules_of ctxt =
  case active ctxt of
      NONE => []
    | SOME r => Symtab.dest (#get r ctxt)
fun named_rules () = named_rules_of (Context.snapshot ())
fun theory_data thy =
  case active (Context.snapshot ()) of
      NONE => []
    | SOME r => List.rev (#reversed_segment r thy)
fun current_data () = theory_data (Theory.current_theory ())

end
