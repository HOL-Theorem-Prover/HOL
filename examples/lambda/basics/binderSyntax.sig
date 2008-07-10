signature binderSyntax =
sig

  include Abbrev

  val cperm_ty : hol_type

  val mk_perm_type : hol_type -> hol_type
  val dest_perm_type : hol_type -> hol_type
  val is_perm_type : hol_type -> bool


  val is_perm_t : term
  val fnpm_t : term
  val pairpm_t : term
  val listpm_t : term
  val stringpm_t : term
  val nullpm_t : term


  val mk_fnpm : term * term -> term

  val type_perm : hol_type -> term * thm


end

(*
   [cperm_ty]  the type of "concrete" permutations, that is lists of pairs
   of strings

   [mk_perm_type ty] returns the type of permutations over ty, i.e., the
   type (string # string) list -> ty -> ty

   [is_perm_t] the term ``is_perm : 'a pm -> bool``

   [fnpm_t] the term ``fnpm : 'a pm -> 'b pm -> ('a -> 'b) pm``

   [pairpm_t] the term ``pairpm : 'a pm -> 'b pm -> ('a # 'b) pm``

   [listpm_t] the term ``listpm : 'a pm -> ('a list) pm``

   [nullpm_t] the term ``K I : 'a pm``

   [type_perm ty] returns the term p that permutes the given ty, and a theorem
   stating |- is_perm p.  If ty is a variable type, then the theorem has the
   same assumption.  If ty is not variable, then a built-in table of perm
   information for types is consulted and the theorem is proved.  Types
   that have no information stored for them are assumed to be permuted
   by the everywhere-identical permutation ``K I``.


*)