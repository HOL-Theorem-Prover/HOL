structure Sref :> Sref =
struct

   type 'a t = {mutex : Mutex.mutex, v : 'a ref}

   fun new v = {mutex = Mutex.mutex(), v = ref v}

   fun gen_update {mutex,v} f =
       Multithreading.synchronized
         "sref.gen_update" mutex
         (fn () => let val (v',b) = f (!v) in v := v'; b end)

   fun update {mutex,v} f =
     Multithreading.synchronized "sref.update" mutex
                                 (fn () => v := f (!v))
   fun value {mutex,v} = !v

end;
