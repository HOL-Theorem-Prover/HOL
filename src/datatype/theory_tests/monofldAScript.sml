open HolKernel Parse boolLib Datatype

val _ = new_theory "monofldA";

val _ = Datatype`rcd = <| myset : 'a -> bool ; sz : num |>`;

val _ = gen_remove_ovl_mapping
          (GrammarSpecials.recfupd_special ^ "myset")
          ``\f x. rcd_myset_fupd f x``

val _ = Parse.add_record_fupdate(
      "myset", Term.inst[beta |-> alpha] ``rcd_myset_fupd``);

val _ = export_theory();
