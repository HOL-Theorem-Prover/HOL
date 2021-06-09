structure foobarLib :> foobarLib =
struct

open HolKernel Abbrev;

(* Updates the set given a delta  *)
fun apply_delta (ThmSetData.ADD(_, th)) thml = th :: thml

(* Defines/Setups the foobar theorem set *)
val {update_global_value = foobar_apply_global_update,
     record_delta = foobar_record_delta,
     get_deltas = foobar_get_deltas,
     get_global_value = foobarthm_list,
     DB = eval_ruleuction_map_by_theory,...} =
    ThmSetData.export_with_ancestry {
      settype = "foobar",
      delta_ops = {apply_to_global = apply_delta, (* How to update the set (globally) *)
                   uptodate_delta = K true,
                   thy_finaliser = NONE,
                   initial_value = [],            (* The initial value of the set *)
                   apply_delta = apply_delta}
    }

(* Add a theorem to the foobar set *)
fun add_foobar_thm th =
    foobar_apply_global_update (curry (op ::) th)

(* Obtains theorems in the foobar set from a given theory *)
fun thy_foobar_thms thyname =
    let
      open ThmSetData
    in
      foobar_get_deltas {thyname = thyname} |> added_thms
    end

(* Get a list of all the theorems in the foobar set *)
val foobar_thms = foobarthm_list

end
