Theory contMonad
Libs
  monadsyntax

(*

   Inspired by usual Haskell definition of the Cont type/monad. We
   don't need to hide the function under a constructor, but this does
   have the advantage of making the type more explicit.

   What in Haskell is Cont r a here becomes ('a,'r) Cont, where 'r is
   the final result type, and doesn't vary as monadic values are composed.
   Though this is a switch, I like that the eventual result type gets to be
   the last parameter.

*)

val _ = temp_add_monadsyntax()

val _ = Datatype`Cont = Cont ((α -> β) -> β)`

Definition runCont_def:  runCont (Cont f) = f
End

Definition CONT_UNIT_def:
  CONT_UNIT (a:α) : (α,ρ)Cont = Cont (λf. f a)
End

Definition CONT_BIND_def:
  CONT_BIND (m : (α,ρ) Cont) (f : α -> (β,ρ) Cont) : (β,ρ) Cont =
    Cont (λ(k:β->ρ). runCont m (λa:α. runCont (f a) (λb:β. k b)))
End

val _ = overload_on ("return", ``CONT_UNIT``)
val _ = overload_on ("monad_bind", ``CONT_BIND``)
val _ = overload_on ("monad_unitbind", ``λm1 m2. CONT_BIND m1 (K m2)``)

val t6 = Q.store_thm(
  "t6",
  `runCont (do x <- return 2; y <- return 3; return (2 + 3) od) SUC = 6`,
  CONV_TAC EVAL)

Definition throw_def:
  throw (v:ρ) : (α,ρ) Cont = Cont (λk. v)
End

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

Definition callCC_def:
  callCC f =
   Cont (λk. runCont (f (λa. Cont (λx. k a))) k)
End

Definition runC_def:
  runC m = runCont m I
End

Definition reset_def:
  (reset : (α,α)Cont -> (α,'r)Cont) = return o runC
End

Definition shift_def:
  shift f = Cont (runC o f)
End


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



