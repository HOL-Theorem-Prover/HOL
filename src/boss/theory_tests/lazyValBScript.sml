Theory lazyValB
Ancestors
  lazyValA

(* lazyValA's own grammar, TypeBase and srw simpset are computed when
   first read, here *)
fun check name b = if b then () else raise Fail ("lazyValB: " ^ name)

val _ = check "grammar"
          (case Parse.grammarDB {thyname = "lazyValA"} of
               SOME (_, tmG) =>
                 isSome (Overload.info_for_name
                           (term_grammar.overload_info tmG) "lazyo")
             | NONE => false)

val _ = check "TypeBase"
          (case TypeBase.thy_typebase {thyname = "lazyValA"} of
               SOME tyb =>
                 isSome (TypeBasePure.prim_get tyb ("lazyValA", "lazyty"))
             | NONE => false)

val _ = check "simpset"
          (case BasicProvers.thy_simpset "lazyValA" of
               SOME ss =>
                 rhs (concl (simpLib.SIMP_CONV ss [] “lazyf (LazyC2 2)”))
                   ~~ “3”
             | NONE => false)
