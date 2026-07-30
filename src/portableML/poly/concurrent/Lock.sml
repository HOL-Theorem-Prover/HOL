structure Lock :> Lock =
struct

  type t = {name : string, mutex : Mutex.mutex}

  fun new name = {name = name, mutex = Mutex.mutex ()}

  fun synchronized {name, mutex} body =
      Multithreading.synchronized name mutex body

end
