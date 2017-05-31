open HolKernel Parse boolLib bossLib;

open monadsyntax

(*

   Inspired by usual Haskell definition of the Cont type/monad. We
   don't need to hide the function under a constructor, but this does
   have the advantage of making the type more explicit.

   What in Haskell is Cont r a here becomes ('a,'r) Cont, where 'r is
   the final result type, and doesn't vary as monadic values are composed.
   Though this is a switch, I like that the eventual result type gets to be
   the last parameter.

*)

val _ = new_theory "contMonad";

val _ = temp_add_monadsyntax()

val _ = Datatype`Cont = Cont ((α -> β) -> β)`

val runCont_def = Define`runCont (Cont f) = f`

val CONT_UNIT_def = Define`
  CONT_UNIT (a:α) : (α,ρ)Cont = Cont (λf. f a)
`;

val CONT_BIND_def = Define`
  CONT_BIND (m : (α,ρ) Cont) (f : α -> (β,ρ) Cont) : (β,ρ) Cont =
    Cont (λ(k:β->ρ). runCont m (λa:α. runCont (f a) (λb:β. k b)))
`;

val _ = overload_on ("return", ``CONT_UNIT``)
val _ = overload_on ("monad_bind", ``CONT_BIND``)
val _ = overload_on ("monad_unitbind", ``λm1 m2. CONT_BIND m1 (K m2)``)

val t6 = Q.store_thm(
  "t6",
  `runCont (do x <- return 2; y <- return 3; return (2 + 3) od) SUC = 6`,
  CONV_TAC EVAL)

val throw_def = Define`
  throw (v:ρ) : (α,ρ) Cont = Cont (λk. v)
`;

val eek_example = ``
  do
    x <- return 2;
    y <- throw [1;2;3];
    z <- return 3;
    return (x + y + z)
  od
``;

val eek_result = save_thm(
  "eek_result",
  EVAL ``runCont ^eek_example (λa. [a])``);

val callCC_def = Define`
  callCC f =
   Cont (λk. runCont (f (λa. Cont (λx. k a))) k)
`;

val runC_def = Define`
  runC m = runCont m I
`;

val reset_def = Define`
  (reset : (α,α)Cont -> (α,'r)Cont) = return o runC
`;

val shift_def = Define`
  shift f = Cont (runC o f)
`;


val okmij1 =
   EVAL ``do
    (a,b) <- reset (do x <- shift (λk. return (3,4));
                       return (x,x)
                    od);
    return (a + b)
   od``

(* from http://okmij.org/ftp/continuations/ContExample.hs

   The k is the continuation that doubles the value, the +1 is not part
   of the continuation because it's outside the reset, and so the result
   below is 41

*)
val okmij_ex1 = save_thm(
  "okmij_ex1",
  EVAL ``runC do
                 n <- reset (do x <- shift (λk. return (k (k 10))) ;
                                return (2 * x)
                             od);
                 return (n + 1)
              od``)

val boringCC = save_thm(
  "boringCC",
  EVAL ``runC do x <- callCC (λk. k 11);
     n <- return (x * 2);
     return (n + 1)
  od``);

val doubleCC = save_thm(
  "doubleCC",
  EVAL ``runC do x <- callCC (λk. return (runC (k 11) + runC (k 10)));
            n <- return (x * 2);
            return (n + 1)
         od``)



val _ = export_theory();
