Theory emitrecord
Ancestors
  basis_emit
Libs
  EmitML

val fooq = `foo = <| n : num ; b : bool |>`;
val _ = Datatype fooq

Definition literal_def:  literal m = <| n := m ; b := T |>
End

val polyrcdq = `prcd = <| m : num ; s : 'a # bool |>`
val _ = Datatype polyrcdq

Definition prcdf_def:
  prcdf (g : 'a -> 'b) r = r with s updated_by (\ (a,b). (g a, ~b))
End

Definition accessor_def:  accessor x = x.n + 1
End

val _ = eSML "emitRecordTest"
             [OPEN ["num"],
              MLSIG "type num = numML.num",
              DATATYPE fooq,
              DATATYPE polyrcdq,
              DEFN prcdf_def,
              DEFN literal_def,
              DEFN accessor_def]
