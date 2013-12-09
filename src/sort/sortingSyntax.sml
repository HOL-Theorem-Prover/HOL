structure sortingSyntax :> sortingSyntax =
struct

open Abbrev HolKernel sortingTheory

val binop =
   HolKernel.syntax_fns "sorting" 2 HolKernel.dest_binop HolKernel.mk_binop

val triop =
   HolKernel.syntax_fns "sorting" 3 HolKernel.dest_triop HolKernel.mk_triop

val quadop =
   HolKernel.syntax_fns "sorting" 4 HolKernel.dest_quadop HolKernel.mk_quadop

val (perm_tm, mk_perm, dest_perm, is_perm) = binop "PERM"
val (sorted_tm, mk_sorted, dest_sorted, is_sorted) = binop "SORTED"
val (qsort_tm, mk_qsort, dest_qsort, is_qsort) = binop "QSORT"
val (qsort3_tm, mk_qsort3, dest_qsort3, is_qsort3) = binop "QSORT3"
val (part_tm, mk_part, dest_part, is_part) = quadop "PART"
val (part3_tm, mk_part3, dest_part3, is_part3) = triop "PART3"
val (partition_tm, mk_partition, dest_partition, is_partition) =
   binop "PARTITION"

end
