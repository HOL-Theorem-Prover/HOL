structure HM_BuildLock :> HM_BuildLock =
struct

(* Moscow ML does not support POSIX file locking.
   This is a no-op implementation. *)

datatype lockhandle = DummyLock

val nolock = DummyLock

fun is_real DummyLock = false

fun release DummyLock = ()

fun acquire {dir, key, warn, diag} = DummyLock

end
