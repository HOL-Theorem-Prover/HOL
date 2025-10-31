Theory monoidTree
(* a theory of trees with values at leaves, and fold
   functions over those trees that give canonical
   results (regardless of tree shape) when function
   is a monoid operation (like APPEND)
*)

Ancestors hol list

Datatype:
  mtree = Lf | Value 'a | Nd mtree mtree
End

Definition map_def[simp]:
  map f Lf = Lf ∧
  map f (Value a) = Value (f a) ∧
  map f (Nd lt rt) = Nd (map f lt) (map f rt)
End

Definition foldl_def[simp]:
  foldl f acc Lf = acc ∧
  foldl f acc (Value a) = f acc a ∧
  foldl f acc (Nd lt rt) = foldl f (foldl f acc lt) rt
End

Definition foldr_def[simp]:
  foldr f acc Lf = acc ∧
  foldr f acc (Value a) = f a acc ∧
  foldr f acc (Nd lt rt) = foldr f (foldr f acc rt) lt
End

(* if f is a monoid, including left-identity, a fold can
   be split up into a top-level application of f to a
   fold with the identity element as initial accumulator
*)
Theorem foldr_nil:
  (∀x y z. f x (f y z) = f (f x y) z) ∧ (∀x. f id x = x) ⇒
  ∀acc. foldr f acc xs = f (foldr f id xs) acc
Proof
  strip_tac >> Induct_on ‘xs’ >> metis_tac[foldr_def]
QED

(* Then, with left *and* right identities, foldr over a
   node can be seen binary application of f to the results
   of fold on both sub-trees *)
Theorem foldr_distrib:
  (∀x y z. f x (f y z) = f (f x y) z) ∧ (∀x. f id x = x) ∧
  (∀x. f x id = x) ⇒
  foldr f id Lf = id ∧ (* strictly redundant; is clause of original def'n *)
  foldr f id (Value a) = a ∧
  foldr f id (Nd lt rt) = f (foldr f id lt) (foldr f id rt)
Proof
  simp[] >> strip_tac >> drule_all_then assume_tac foldr_nil >>
  pop_assum (once_rewrite_tac o single) >> simp[]
QED

(* ----------------------------------------------------------------------
    Instances: lists, in particular
   ---------------------------------------------------------------------- *)

Type app_list = “:'a list mtree”

Overload flatten = “foldr APPEND []”
Overload "Append" = “Nd : 'a app_list -> 'a app_list -> 'a app_list”
Overload "+++" = “Append”

Theorem flatten_thm[simp]:
  flatten (Lf:'a app_list) = [] ∧
  flatten (Value a : 'a app_list) = a ∧
  flatten (lt +++ rt : 'a app_list) = flatten lt ++ flatten rt
Proof
  irule foldr_distrib >> simp[]
QED

Theorem critical_pair1[simp]:
  foldr (++) (flatten ys) xs = flatten xs ++ flatten ys
Proof
  irule foldr_nil >> simp[]
QED

(* pragmatically, given behaviour of simplifier, this may not be
   necessary *)
Theorem critical_pair2[simp]:
  foldr (++) (flatten ys ++ flatten zs) xs =
  (flatten xs ++ flatten ys) ++ flatten zs
Proof
  rewrite_tac[GSYM APPEND_ASSOC] >> irule foldr_nil >> simp[]
QED
