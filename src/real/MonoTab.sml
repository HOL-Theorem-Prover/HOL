(* Monomial-keyed tables for SOSLib.                                     *)
(*                                                                       *)
(* This instantiation lives in its own file rather than in SOSLib.sml    *)
(* because mosml needs Table.ui named on the compiler command line for   *)
(* a functor application (its dependency auto-detection misses them),    *)
(* and a Holmakefile rule supplying it bypasses Holmake's quote filter.  *)
(* SOSLib.sml contains HOL quotations, so it cannot carry such a rule;   *)
(* this file deliberately contains none.  See src/real/Holmakefile.      *)

structure MonoTab = Table(
  type key = int Termtab.table

  (* Canonical monomial comparison for use as map keys *)
  fun mono_compare (m1:key, m2:key) =
      let val l1 = Termtab.dest m1
          val l2 = Termtab.dest m2
          fun cmp ([], []) = EQUAL
            | cmp ([], _)  = LESS
            | cmp (_, [])  = GREATER
            | cmp ((v1,p1)::t1, (v2,p2)::t2) =
              case Term.compare(v1,v2) of
                  EQUAL => (case Int.compare(p1,p2) of
                                EQUAL => cmp(t1,t2)
                              | ord => ord)
                | ord => ord
      in cmp(l1, l2)
      end

  val ord = mono_compare
  fun pp _ = HOLPP.add_string "<monomial>"
)
