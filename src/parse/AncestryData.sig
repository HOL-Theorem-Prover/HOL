signature AncestryData =
sig
  type ('delta,'value,'extra) adata_info = {
    tag : string, initial_values : (string * 'value) list,
    extra : 'extra,
    apply_delta : 'delta -> 'value -> 'value,
    delta_side_effects : 'delta -> unit
  }
  val make : ('delta, 'value, {thyname:string} -> 'delta) adata_info  ->
             { merge : string list -> 'value,
               DB : {thyname : string} -> 'value,
               parents : {thyname : string} -> string list,
               set_parents : string list -> 'value
             }




end
