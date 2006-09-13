(module PreKernelRecords mzscheme
  (provide (all-defined))
  
  (define-struct error_record
                 (origin_structure
                  origin_function
                  message))
  
  (define-struct temp-struct
                 (name
                  trace_level
                  default
                  max))
  
  )