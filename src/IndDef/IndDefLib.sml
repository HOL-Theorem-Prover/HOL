structure IndDefLib :> IndDefLib =
struct

local open IndDefRules in end;

open Abbrev;

(*---------------------------------------------------------------------------
     Will also want to allow re-definition of const(s).
 ---------------------------------------------------------------------------*)

fun new_inductive_definition M =
  InductiveDefinition.new_inductive_definition 
       InductiveDefinition.bool_monoset M;


end
