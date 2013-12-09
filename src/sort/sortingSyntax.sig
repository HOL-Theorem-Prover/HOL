signature sortingSyntax =
sig

   include Abbrev

   val part3_tm: term
   val part_tm: term
   val partition_tm: term
   val perm_tm: term
   val qsort3_tm: term
   val qsort_tm: term
   val sorted_tm: term

   val dest_part: term -> term * term * term * term
   val dest_part3: term -> term * term * term
   val dest_partition: term -> term * term
   val dest_perm: term -> term * term
   val dest_qsort: term -> term * term
   val dest_qsort3: term -> term * term
   val dest_sorted: term -> term * term

   val is_part: term -> bool
   val is_part3: term -> bool
   val is_partition: term -> bool
   val is_perm: term -> bool
   val is_qsort: term -> bool
   val is_qsort3: term -> bool
   val is_sorted: term -> bool

   val mk_part: term * term * term * term -> term
   val mk_part3: term * term * term -> term
   val mk_partition: term * term -> term
   val mk_perm: term * term -> term
   val mk_qsort: term * term -> term
   val mk_qsort3: term * term -> term
   val mk_sorted: term * term -> term
end
