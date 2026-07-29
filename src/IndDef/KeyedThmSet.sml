structure KeyedThmSet :> KeyedThmSet =
struct

open HolKernel

datatype clause_part = Hypothesis | Conclusion

type keyed_thm_map = thm list KNametab.table

datatype keyed_thm_set = KeyedThmSet of
  {add : thm -> unit,
   export_thm : string -> unit,
   thy_thms : string -> thm list,
   get_map : unit -> keyed_thm_map,
   map_by_theory : {thyname : string} -> keyed_thm_map option}

fun listdict_add (d, k, e) =
    case KNametab.lookup d k of
      NONE => KNametab.update (k,[e]) d
    | SOME l => KNametab.update (k,e::l) d

fun new {settype, key_part} =
  let
    val (part_name, select) =
      case key_part of
          Hypothesis => ("hypothesis", fn (h, _ : term) => h)
        | Conclusion => ("conclusion", fn (_ : term, c) => c)
    (* Errors are reported against this structure and the entry point
       actually taken; the set type identifies the feature at fault, so
       a user who wrote Theorem foo[coinduction] sees "[coinduction]"
       whichever of add/export_thm/apply_delta was on the stack. *)
    fun err origin message =
      mk_HOL_ERR "KeyedThmSet" origin ("[" ^ settype ^ "] " ^ message)
    fun theorem_keys origin theorem =
      let
        val theorem_tm = concl theorem
        val (_, body) = boolSyntax.strip_forall theorem_tm
        val consequences =
          #2 (boolSyntax.dest_imp body)
          handle HOL_ERR _ =>
            raise err origin
              ("theorems must have the form " ^
               "`!vs. premises ==> clauses'; got: " ^
               Parse.term_to_string theorem_tm)
        fun key_of clause =
          (clause |> boolSyntax.strip_forall |> #2 |> boolSyntax.dest_imp
                  |> select |> strip_comb |> #1 |> dest_thy_const
                  |> (fn {Name, Thy, ...} => {Name = Name, Thy = Thy}))
          handle HOL_ERR _ =>
            raise err origin
              ("theorem clauses must have the form " ^
               "`!vs. hyp ==> concl' with the " ^ part_name ^
               " headed by a constant; got: " ^ Parse.term_to_string clause)
      in
        map key_of (boolSyntax.strip_conj consequences)
      end
    fun add0 origin theorem dict =
      List.foldl (fn (key, result) => listdict_add (result, key, theorem))
        dict (theorem_keys origin theorem)
    fun apply_delta0 origin (ThmSetData.ADD (_, theorem)) dict =
          add0 origin theorem dict
      | apply_delta0 _ _ dict = dict
    val {update_global_value, record_delta, get_deltas, get_global_value,
         DB, ...} =
      ThmSetData.export_with_ancestry {
        settype = settype,
        delta_ops = {apply_to_global = apply_delta0 "apply_delta",
                     uptodate_delta = K true,
                     thy_finaliser = NONE,
                     initial_value = KNametab.empty,
                     apply_delta = apply_delta0 "apply_delta"}}
    fun add theorem = update_global_value (add0 "add" theorem)
    (* Validate first, persist next, and publish last.  This leaves neither
       a bad descendant delta nor a process-local entry when persistence
       rejects the update. *)
    fun export_thm name =
      let
        val delta = ThmSetData.mk_add name
        val value = apply_delta0 "export_thm" delta (get_global_value ())
      in
        record_delta delta;
        update_global_value (K value)
      end
    fun thy_thms thyname =
      ThmSetData.added_thms (get_deltas {thyname = thyname})
  in
    KeyedThmSet
      {add = add, export_thm = export_thm, thy_thms = thy_thms,
       get_map = get_global_value, map_by_theory = DB}
  end

fun add (KeyedThmSet {add, ...}) = add
fun export_thm (KeyedThmSet {export_thm, ...}) = export_thm
fun thy_thms (KeyedThmSet {thy_thms, ...}) = thy_thms
fun get_map (KeyedThmSet {get_map, ...}) = get_map
fun map_by_theory (KeyedThmSet {map_by_theory, ...}) = map_by_theory

end (* struct *)
