val _ = case !buildheap_cline_mt of
            NONE => ()
          | SOME i => Multithreading.max_threads_update i
;
