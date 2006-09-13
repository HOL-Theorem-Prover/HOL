(module Feedback mzscheme
  
  (require "locn.scm"
           (prefix Globals: "Globals.scm")
           "records.scm"
           "PreKernelRecords.scm")
  
  (require (prefix srfi: (lib "1.ss" "srfi"))
           (lib "list.ss")
           (lib "plt-match.ss"))
  
  (provide (all-defined-except ERR))
  
  (define mk_HOL_ERR make-error_record)
  
  (define (mk_HOL_ERRloc s1 s2 locn s3)
    (make-error_record s1 s2
                       (string-append (toString locn)
                                      ":\n"
                                      s3)))
  
  (define (ERR s2 s3)
    (mk_HOL_ERR "Feedback" s2 s3))
  
  (define (output port str)
    (display str port))
  
  (define flush_out flush-output)
  
  ;quote is renamed to avoid conflicting with the Scheme quote
  (define (string-quote s)
    (string-append "\"" s "\""))
  
  (define (assoc1 item lst)
    (cond ((null? lst)
           'NONE)
          ((equal? item
                   (vector-ref (car lst) 0))
           (make-SOME (car lst)))
          (else
           (assoc1 item (cdr lst)))))
  
  (define emit_ERR
    (box #t))
  (define emit_MESG
    (box #t))
  (define emit_WARNING
    (box #t))
  
  (define ERR_outstream
    (box (current-error-port)))
  (define MESG_outstream
    (box (current-output-port)))
  (define WARNING_outstream
    (box (current-output-port)))
  
  (define (format_err_rec err_rec)
    (string-append "at "
                   (error_record-origin_structure err_rec)
                   "."
                   (error_record-origin_function err_rec)
                   ":\n"
                   (error_record-message err_rec)))
  
  (define (format_ERR err_rec)
    (string-append "\nException raised "
                   (format_err_rec err_rec)
                   "\n"))
  
  (define (format_MESG s)
    (string-append "<<HOL message: "
                   s
                   ">>\n"))
  
  (define (format_WARNING structName fnName mesg)
    (string-append "<<HOL warning: "
                   structName
                   "."
                   fnName
                   ": "
                   mesg
                   ">>\n"))
  
  (define ERR_to_string
    (box format_ERR))
  (define MESG_to_string
    (box format_MESG))
  (define WARNING_to_string
    (box format_WARNING))
  
  (define (output_ERR s)
    (when (unbox emit_ERR)
      (output (unbox ERR_outstream) s)
      (flush_out (unbox ERR_outstream))))
  
  (define (exn_to_string e)
    (cond ((error_record? e)
           ((unbox ERR_to_string)
            e))
          ((exn:break? e)
           (raise e))
          (else
           (exn-message e))))
  
  (define (Raise e)
    (output_ERR (exn_to_string e))
    (raise e))
  
  (define (fail)
    (raise (mk_HOL_ERR "??" "??" "fail")))
  (define (failwith s)
    (raise (mk_HOL_ERR "??" "failwith" s)))
  
  
  (define (wrap_exn s f exn)
    (cond ((exn:break? exn)
           (raise exn))
          ((error_record? exn)
           (mk_HOL_ERR s f (format_err_rec exn)))
          (else
           (mk_HOL_ERR s f (exn-message exn)))))
  
  (define (wrap_exn_loc s f l exn)
    (cond ((exn:break? exn)
           (raise exn))
          ((error_record? exn)
           (mk_HOL_ERRloc s f l (format_err_rec exn)))
          (else
           (mk_HOL_ERRloc s f l (exn-message exn)))))
  
  (define (HOL_MESG s)
    (when (unbox emit_MESG)
      (output (unbox MESG_outstream)
              ((unbox MESG_to_string) s))
      (flush_out (unbox MESG_outstream))))
  
  (define (HOL_PROGRESS_MESG b f x)
    (let ((start (vector-ref b 0))
          (finish (vector-ref b 1)))
      (if (unbox emit_MESG)
          (let ((p (unbox MESG_outstream)))
            (output p
                    (string-append "<<HOL message: "
                                   start))
            (flush_out p)
            (output p
                    (string-append finish
                                   ">>\n"))
            (flush_out p))
          (f x))))
  
  (define (HOL_WARNING s1 s2 s3)
    (when (unbox emit_WARNING)
      (output (unbox WARNING_outstream)
              ((unbox WARNING_to_string) s1 s2 s3))
      (flush_out (unbox WARNING_outstream))))
  
  (define (HOL_WARNINGloc s1 s2 locn s3)
    (HOL_WARNING s1 s2
                 (string-append (toString locn)
                                ":\n"
                                s3)))
  
  (define-struct TRFP (get set))
  
  (define (trfp_set t)
    (TRFP-set))
  (define (trfp_get t)
    ((TRFP-get)))
  
  (define (ref2trfp r)
    (make-TRFP (lambda () (unbox r))
               (lambda (i) (set-box! r i))))
  
  (define-struct trace_record
    (name value default maximum))
  
  (define trace_list
    (box '()))
  
  (define (find_record n)
    (cond ((srfi:find-tail (lambda (r)
                             (equal? (trace_record-name r) n))
                           (unbox trace_list))
           => (lambda (pair) (car pair)))
          (else 'NONE)))
  
  (define (register_trace t)
    (let ((nm (vector-ref t 0))
          (r (vector-ref t 1))
          (max (vector-ref t 2)))
      (cond ((or (< (unbox r) 0)
                 (< max 0))
             (raise (ERR "register_trace"
                         "Can't have trace values less than zero.")))
            ((eq? (find_record nm) 'NONE)
             (set-box! trace_list
                       (cons (make-trace_record nm
                                                (ref2trfp r)
                                                (unbox r)
                                                max)
                             (unbox trace_list))))
            (else
             (raise (ERR "register_trace"
                         (string-append "Already a trace "
                                        (string-quote nm)
                                        " registered.")))))))
  
  (define (register_ftrace t)
    (let ((nm (vector-ref t 0))
          (get (vector-ref (vector-ref t 1) 0))
          (set (vector-ref (vector-ref t 1) 1))
          (max (vector-ref t 2)))
      (let ((default (get)))
        (cond ((or (< default 0)
                   (< max 0))
               (raise (ERR "register_ftrace"
                           "Can't have trace values less than zero.")))
              ((eq? (find_record nm) 'NONE)
               (set-box! trace_list
                         (cons (make-trace_record nm
                                                  (make-TRFP get set)
                                                  default
                                                  max)
                               (unbox trace_list))))
              (else
               (raise (ERR "register_ftrace"
                           (string-append "Already a trace "
                                          (string-quote nm)
                                          " registered."))))))))
  
  (define (register_btrace t)
    (let ((nm (vector-ref t 0))
          (bref (vector-ref t 1)))
      (if (eq? (find_record nm) 'NONE)
          (set-box! trace_list
                    (cons (make-trace_record nm
                                             (make-TRFP (lambda ()
                                                          (if (unbox bref) 1 0))
                                                        (lambda (i)
                                                          (set-box! bref
                                                                    (> i 0))))
                                             (if (unbox bref) 1 0)
                                             1)
                          (unbox trace_list)))
          (raise (ERR "register_btrace"
                      (string-append "Already a trace "
                                     (string-quote nm)
                                     " registered."))))))
  
  (define (traces)
    (mergesort (map (lambda (t)
                      (make-temp-struct (trace_record-name t)
                                        (trfp_get (trace_record-value t))
                                        (trace_record-default t)
                                        (trace_record-maximum t)))
                    (unbox trace_list))
               (lambda (r1 r2)
                 (string<? (trace_record-name r1)
                           (trace_record-name r2)))))
  
  (define (set_trace nm newvalue)
    (match (find_record nm)
      ((struct SOME ((struct trace_record (_ value _ maximum))))
       (cond ((> newvalue maximum)
                   (raise (ERR "set_trace"
                               (string-append "Trace "
                                              (string-quote nm)
                                              " can't be set that high."))))
                  ((< newvalue 0)
                   (raise (ERR "set_trace"
                               (string-append "Trace "
                                              (string-quote nm)
                                              " can't be set less than 0."))))
                  (else
                   ((trfp_set value) newvalue))))
      ('NONE
        (raise (ERR "set_trace"
                    (string-append "No trace "
                                   (string-quote nm)
                                   " is registered"))))))
  
  (define (reset_trace nm)
    (match (find_record nm)
      ((struct SOME ((struct trace_record (_ value default _))))
       ((trfp_set value) default))
      ('NONE
        (raise (ERR "reset_trace"
                    (string-append "No trace "
                                   (string-quote nm)
                                   " is registered"))))))
  
  (define (reset_traces)
    (apply (lambda (t)
             (let ((value (trace_record-value t))
                   (default (trace_record-default t)))
               ((trfp_set value) default)))
           (unbox trace_list)))
  
  (define (current_trace s)
    (match (find_record s)
      ((struct SOME ((struct trace_record (_ value _ _))))
       (trfp_get value))
      ('NONE
        (raise (ERR "current_trace"
                    (string-append "No trace "
                                   (string-quote s)
                                   " is registered"))))))
  
  (define trace
    (match-lambda*
      ((list (vector nm i) f x)
       (match (find_record nm)
         ('NONE
           (raise (ERR "trace"
                       (string-append "No trace "
                                      (string-quote nm)
                                      " is registered"))))
         ((struct SOME ((struct trace_record (_ value _ maximum))))
          (cond ((> i maximum)
                 (raise (ERR "trace"
                             (string-append "Trace "
                                            (string-quote nm)
                                            " can't be set that high."))))
                ((< i 0)
                 (raise (ERR "set_trace"
                             (string-append "Trace "
                                            (string-quote nm)
                                            " can't be set less than 0."))))
                (else
                 (let* ((init (trfp_get value))
                        (dummy ((trfp_set value) i))
                        (y (with-handlers (((lambda (x) #t)
                                            (lambda (e)
                                              ((trfp_set value) init)
                                              (raise e))))
                             (f x))))
                   ((trfp_set value) init)
                   y))))))))
  
  (define (get_tracefn nm)
    (match (find_record nm)
      ('NONE
        (raise (ERR "get_tracefn"
                    (string-append "No trace "
                                   (string-quote nm)
                                   " is registered"))))
      ((struct SOME ((struct trace_record (_ (struct TRFP (get _)) _ _))))
       get)))
  
  (register_btrace (vector "assumptions" Globals:show_assums))
  (register_btrace (vector "numeral types" Globals:show_numeral_types))
  
  (let* ((v Globals:show_types_verbosely)
         (t Globals:show_types)
         (get (lambda ()
                (cond ((unbox v)
                       2)
                      ((unbox t)
                       1)
                      (else
                       0))))
         (set (lambda (i)
                (cond ((= i 0)
                       (set-box! v #f)
                       (set-box! t #f))
                      ((= i 1)
                       (set-box! v #f)
                       (set-box! t #t))
                      (else
                       (set-box! v #t)
                       (set-box! t #t))))))
    (register_ftrace (vector "types" (vector get set) 2)))
  
  )