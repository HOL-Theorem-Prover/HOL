(module Sig mzscheme
  
  (require (lib "plt-match.ss")
           (lib "unit.ss")
           (only (lib "1.ss" "srfi")
                 partition
                 fold))
  
  (require "records.scm"
           "0Records.scm"
           "PreKernelRecords.scm")
  
  (require (prefix KernelTypes. "KernelTypes.scm")
           (prefix Lib. "Lib.scm"))
  
  (provide (all-defined))
  
  (define SIG
    (unit
      (import key
              ERR
              table_size)
      (export id_of
              insert
              delete
              lookup
              resolve
              add_witness
              app
              slice
              filter
              scope
              del_segment
              anachronize
              all_entries)
      
      (define (id_of x)
        (key (vector-ref x 0)))
      (define (retire const)
        (KernelTypes.retire (key const)))
      
      (define theSig
        (make-vector table_size ()))
      
      (define hash
        (Lib.hash table_size))
      
      (define (insert item)
        (letrec ((clobbered (box #f))
                 (p (KernelTypes.dest_id (key item)))
                 (i (hash (vector-ref p 0)))
                 (entry (vector item 'NONE (box #t)))
                 (add
                  (match-lambda
                    ((list)
                     (list entry))
                    ((list-rest e rst)
                     (if (equal? p
                                 (KernelTypes.dest_id (key (vector-ref e 0))))
                         (begin (retire (vector-ref e 0))
                                (set-box! clobbered #t)
                                (cons entry rst))
                         (cons e (add rst)))))))
          (vector-set! theSig i
                       (add (vector-ref theSig i)))
          ((if (unbox clobbered)
               make-CLOBBER
               make-INITIAL)
           entry)))
      
      (define add_witness
        (match-lambda
          ((vector name theory wit)
           (letrec ((p (vector name theory))
                    (i (hash name))
                    (L (vector-ref theSig i))
                    (get
                     (match-lambda
                       ((list)
                        (raise (ERR "add_witness" "no such constant")))
                       ((list-rest (vector const witness utd) rst)
                        (if (equal? p
                                    (KernelTypes.dest_id (key const)))
                            (cons (vector const utd (make-SOME wit))
                                  rst)
                            (cons (vector const witness utd)
                                  (get rst)))))))
             (vector-set! theSig i (get L))))))
      
      (define delete
        (match-lambda
          ((vector p)
           (with-handlers ((error_record? #f))
             (letrec ((name (vector-ref p 0))
                      (i (hash name))
                      (del
                       (match-lambda
                         ((list)
                          (raise (ERR "" "")))
                         ((list-rest (vector const witness utd) rst)
                          (if (equal? p
                                      (KernelTypes.dest_id (key const)))
                              (begin (retire const)
                                     rst)
                              (cons (vector const witness utd)
                                    (del rst)))))))
               (vector-set! theSig i 
                            (del (vector-ref theSig i)))
               #t)))))
      
      (define lookup
        (match-lambda
          ((vector p)
           (letrec ((name (vector-ref p 0))
                    (look
                     (match-lambda
                       ((list)
                        'NONE)
                       ((list-rest e rst)
                        (if (equal? p (KernelTypes.dest_id (id_of e)))
                            (make-SOME e)
                            (look rst))))))
             (look (vector-ref theSig (hash name)))))))
      
      (define (resolve name)
        (letrec ((look
                  (match-lambda
                    ((list)
                     (list))
                    ((list-rest e rst)
                     (if (equal? name
                                 (KernelTypes.name_of (id_of e)))
                         (cons e (look rst))
                         (look rst))))))
          (look (vector-ref theSig (hash name)))))
      
      (define (app f)
        (Lib.for_se 0 (- table_size 1)
                    (lambda (i)
                      (vector-set! theSig i
                                   (f (vector-ref theSig i))))))
      
      (define (filter P)
        (app (Lib.gather P)))
      (define (scope P)
        (app (call-with-values (lambda () (partition P))
                               append)))
      
      (define (del_segment seg e)
        (if (equal? seg (KernelTypes.seg_of (id_of e)))
            (begin (retire (vector-ref e 0)
                           #f))
            #t))
      
      (define (app_se f)
        (Lib.for_se 0 (- table_size 1)
                (lambda (i)
                  (apply f (vector-ref theSig i)))))
      
      (define (anachronize thy)
        (let ((unset_utd
               (match-lambda
                 ((vector const utd witness)
                  (if (equal? (KernelTypes.seg_of (key const))
                              thy)
                      (set-box! utd #f))))))
          (app_se unset_utd)))
      
      (define (foldl f b)
        (fold (match-lambda
                ((vector L A)
                 (fold f A L)))
              b theSig))
      
      (define (slice segment)
        (fold (match-lambda
                ((vector e D)
                 (if (equal? segment
                             (KernelTypes.seg_of (id_of e)))
                     (cons e D)
                     D)))
              ()))
      
      (define (all_entries)
        (foldl cons '()))
      
      ))
  
  )
