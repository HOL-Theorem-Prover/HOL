open HolKernel Datatype
val _ = new_theory"foo260";
val _ = Datatype`foo = <| f : bool |>`;
val _ = export_theory();
