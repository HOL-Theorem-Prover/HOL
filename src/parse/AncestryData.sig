signature AncestryData =
sig
  type ('delta,'value) adata_info = {
    tag : string, initial_values : (string * 'value) list,
    apply_delta : 'delta -> 'value -> 'value
  }

  type ('delta,'value) fullresult =
       { merge : string list -> 'value option,
         DB : {thyname : string} -> 'value option,
         get_deltas : {thyname : string} -> 'delta list,
         record_delta : 'delta -> unit,
         parents : {thyname : string} -> string list,
         set_parents : string list -> 'value option,
         get_global_value : unit -> 'value,
         update_global_value : ('value -> 'value) -> unit }

  val make : { info : ('delta, 'value) adata_info,
               get_deltas : {thyname:string} -> 'delta list,
               delta_side_effects : 'delta -> unit } ->
             { merge : string list -> 'value option,
               DB : {thyname : string} -> 'value option,
               parents : {thyname : string} -> string list,
               set_parents : string list -> 'value option
             }

  val fullmake : { adinfo : ('delta, 'value) adata_info,
                   uptodate_delta : 'delta -> bool,
                   sexps : { dec : 'delta ThyDataSexp.dec,
                             enc : 'delta ThyDataSexp.enc },
                   globinfo : {apply_to_global : 'delta -> 'value -> 'value,
                               initial_value : 'value}} ->
                 ('delta,'value) fullresult

end
