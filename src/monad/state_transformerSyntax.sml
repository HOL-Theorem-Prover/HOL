structure state_transformerSyntax :> state_transformerSyntax =
struct

open Abbrev HolKernel state_transformerTheory

(*---------------------------------------------------------------------------*)

fun syntax n m d = HolKernel.syntax_fns "state_transformer" n m d

val (unit_tm,mk_unit,dest_unit,is_unit) =
   syntax 2
      (fn tm1 => fn e => fn tm2 =>
          (HolKernel.dest_monop tm1 e tm2,
           tm2 |> Term.type_of |> Type.dom_rng |> fst))
      (fn tm1 => fn (tm2, ty) =>
          Term.mk_comb
             (Term.inst [Type.alpha |-> ty, Type.beta |-> Term.type_of tm2] tm1,
              tm2))
      "UNIT"

val (join_tm,mk_join,dest_join,is_join) =
   syntax 2 HolKernel.dest_monop HolKernel.mk_monop "JOIN"

val (bind_tm,mk_bind,dest_bind,is_bind) =
   syntax 3 HolKernel.dest_binop HolKernel.mk_binop "BIND"

val (mmap_tm,mk_mmap,dest_mmap,is_mmap) =
   syntax 3 HolKernel.dest_binop HolKernel.mk_binop "MMAP"

val state_ty = Type.mk_vartype "'state"

val (for_tm,mk_for,dest_for,is_for) =
   syntax 2
      (fn tm1 => fn e => fn tm2 =>
          let
             val a = HolKernel.dest_monop tm1 e tm2
          in
             case pairSyntax.strip_pair a of
                [i, j, b] => (i, j, b)
              | _ => raise e
          end)
      (fn tm => fn (i, j, b) =>
         let
            val ty = b |> Term.type_of
                       |> Type.dom_rng |> snd
                       |> Type.dom_rng |> fst
         in
            Term.mk_comb (Term.inst [state_ty |-> ty] tm,
                          pairSyntax.list_mk_pair [i, j, b])
         end)
      "FOR"

end
