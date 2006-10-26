(module Lexis mzscheme
  
  (provide allowed_user_type_var)
  
  (define (ordof string place)
    (char->integer
     (string-ref string place)))
  
  (define prime (ordof "'" 0))
  
  (define bzero 0)
  (define bone 1)
  
  (define alphabet
    (make-vector 128 bzero))
  (define tyvar_ids
    (make-vector 128 bzero))
  
  (define (allowed_user_type_var str)
    (define (loop i)
      (and (equal? (vector-ref tyvar_ids (ordof str i))
                   bone)
           (loop (add1 i))))
    (and (with-handlers
             (((lambda (x) #t) #f))
           (equal? (ordof str 0)
                   prime))
         (with-handlers
             (((lambda (x) #t) #f))
           (equal? (vector-ref alphabet (ordof str 1))
                   bone))
         (with-handlers
             (((lambda (x) #t) #t))
           (loop 2)))))

