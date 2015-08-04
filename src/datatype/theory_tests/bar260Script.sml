open HolKernel Datatype foo260Theory;
val _ = new_theory"bar260";
val _ = Datatype`foo = <| f : bool |>`;
val _ = export_theory();
