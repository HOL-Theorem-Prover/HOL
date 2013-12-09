structure state_transformerSyntax :> state_transformerSyntax =
struct

open Abbrev HolKernel state_transformerTheory

val ERR = Feedback.mk_HOL_ERR "state_transformerSyntax"

(*---------------------------------------------------------------------------*)

fun syntax n m d = HolKernel.syntax_fns "state_transformer" n m d

val s1 = syntax 2 HolKernel.dest_monop HolKernel.mk_monop
val s2 = syntax 3 HolKernel.dest_binop HolKernel.mk_binop

fun mk_monad_type (ty1, ty2) = ty2 --> pairSyntax.mk_prod (ty1, ty2)

local
   val err = ERR "dest_monad_type" "not a monad type"
in
   fun dest_monad_type ty =
      let
         val (ty1, ty2) = Lib.with_exn Type.dom_rng ty err
         val ty3 as (_, ty4) = Lib.with_exn pairSyntax.dest_prod ty2 err
         val _ = ty1 = ty4 orelse raise err
      in
         ty3
      end
end

val state_ty = Type.mk_vartype "'state"

val (unit_tm, mk_unit, dest_unit, is_unit) =
   syntax 2
      (fn tm1 => fn e => fn tm2 =>
          (HolKernel.dest_monop tm1 e tm2,
           tm2 |> Term.type_of |> Type.dom_rng |> fst))
      (fn tm1 => fn (tm2, ty) =>
          Term.mk_comb
             (Term.inst [Type.alpha |-> ty, Type.beta |-> Term.type_of tm2] tm1,
              tm2))
      "UNIT"

val (widen_tm, mk_widen, dest_widen, is_widen) =
   syntax 2
      (fn tm1 => fn e => fn tm2 =>
          (HolKernel.dest_monop tm1 e tm2,
           fst (pairSyntax.dest_prod
                   (snd (dest_monad_type (Term.type_of tm2))))))
      (fn tm1 => fn (tm2, ty) =>
          let
             val (ty1, ty2) = dest_monad_type (Term.type_of tm2)
          in
             Term.mk_comb
                (Term.inst [Type.alpha |-> ty1,
                            Type.beta |-> ty,
                            state_ty |-> ty2] tm1, tm2)
          end)
      "WIDEN"

val (join_tm, mk_join, dest_join, is_join) = s1 "JOIN"
val (read_tm, mk_read, dest_read, is_read) = s1 "READ"
val (write_tm, mk_write, dest_write, is_write) = s1 "WRITE"
val (narrow_tm, mk_narrow, dest_narrow, is_narrow) = s2 "NARROW"
val (bind_tm, mk_bind, dest_bind, is_bind) = s2 "BIND"
val (mmap_tm, mk_mmap, dest_mmap, is_mmap) = s2 "MMAP"

val (for_tm, mk_for, dest_for, is_for) =
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
