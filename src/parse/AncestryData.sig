signature AncestryData =
sig
  type ('delta,'value) adata_info = {
    tag : string, initial_values : (string * 'value) list,
    apply_delta : 'delta -> 'value -> 'value
  }
  val make : { info : ('delta, 'value) adata_info,
               get_deltas : {thyname:string} -> 'delta list,
               delta_side_effects : 'delta -> unit } ->
             { merge : string list -> 'value,
               DB : {thyname : string} -> 'value,
               parents : {thyname : string} -> string list,
               set_parents : string list -> 'value
             }
(*
  val fullmake : { info : ('delta, 'value) adata_info,
                   sexps : { dec : 'delta ThmDataSexp.dec,
                             enc : 'delta ThmDataSexp.enc },
                   apply_to_global : 'delta -> 'value -> 'value} ->
                 { merge : string list -> 'value,
                   DB : {thyname : string} -> 'value,
                   get_deltas : {thyname : string} -> 'delta list,
                   record_delta : 'delta -> unit,
                   parents : {thyname : string} -> string list,
                   set_parents : string list -> 'value,
                   get_global_value : unit -> 'value,
                   update_global_value : ('value -> 'value) -> unit }
*)

end
