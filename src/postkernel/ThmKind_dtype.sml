structure ThmKind_dtype =
struct

type thm = Thm.thm
datatype t = Thm of thm | Axiom of string Nonce.t * thm | Defn of thm

end
