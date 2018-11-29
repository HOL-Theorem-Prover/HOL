structure Sref :> Sref =
struct

   type 'a t = {mutex : Mutex.mutex, v : 'a ref}

   fun new v = {mutex = Mutex.mutex(), v = ref v}

   fun update {mutex,v} f =
     Multithreading.synchronized "sref.update" mutex
                                 (fn () => v := f (!v))
   fun value {mutex,v} = !v

end;
