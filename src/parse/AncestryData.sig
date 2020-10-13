signature AncestryData =
sig

  val make :  {tag : string, initial_values : (string * 'value) list,
               get_delta : {thyname : string} -> 'delta,
               apply_delta : 'delta -> 'value -> 'value,
               delta_side_effects : 'delta -> unit
               } ->
              { merge : string list -> 'value,
                DB : {thyname : string} -> 'value,
                parents : {thyname : string} -> string list,
                set_parents : string list -> 'value
              }


end
