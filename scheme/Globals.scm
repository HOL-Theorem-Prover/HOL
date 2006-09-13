(module Globals mzscheme
  
  (require "PreKernelRecords.scm")
  (require (lib "plt-match.ss"))
  
  (provide (all-defined))
  
  (define HOLDIR ".")
  
  (define show_assums (box #f))
  (define show_tags (box #f))
  (define show_axioms (box #t))
  (define show_scrub (box #t))
  
  (define output_HOL_ERR
    (box
     (match-lambda
       ((struct error_record (origin_structure origin_function message))
        (display (string-append "\nException raised at "
                                origin_structure
                                "."
                                origin_function
                                ":\n"
                                message
                                "\n"))
        (flush-output)))))
  
  (define type_pp_prefix
    (box "`"))
  (define type_pp_suffix
    (box "`"))
  (define term_pp_prefix
    (box "`"))
  (define term_pp_suffix
    (box "`"))
  
  ;(pretty-print-columns 72)
  ;(pretty-print-depth #f)
  
  (define show_numeral_types (box #f))
  (define show_types_verbosely (box #f))
  (define show_types (box #f))
  
  (define goal_line
    (box "------------------------------------"))
  
  (define guessing_tyvars
    (box #t))
  
  (define guessing_overloads
    (box #t))
  
  (define notify_on_tyvar_guess
    (box #t))
  
  (define old
    (let ((c 0))
      (lambda (s)
        (begin0
          (string-append "old"
                         (number->string c)
                         "->"
                         s
                         "<-old")
          (set! c (add1 c))))))
  
  (define priming
    (box 'NONE))
  
  (define allow_schema_definition
    (box #f))
  
  (define print_thy_loads
    (box #f))
  
  (define interactive
    (box #f))
  
  ;(define hol_clock ???)
  
  (define exportMLPath
    (box (path->string
          (build-path HOLDIR "src/theoryML/"))))
  
  )