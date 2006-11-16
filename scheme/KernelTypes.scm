(module KernelTypes mzscheme
  
  (provide (all-defined))
  
  (require "0Records.scm"
           (only "Globals.scm" old)
           (only "Lib.scm" stringquote))
  
  (require (lib "plt-match.ss")
           (lib "compare.ss" "srfi" "67"))
  
  (define (mk_id p)
    (box p))
  
  (define (dest_id p)
    (unbox (car dest_id)))
  
  (define (name_of id)
    (vector-ref (dest_id id) 0))
  (define (seg_of id)
    (vector-ref (dest_id id) 1))
  
  (define (retire r)
    (match (dest_id r)
      ((vector n t)
       (set-box! r (vector (old n) t)))))
  
  (define same_id equal?)
  
  (define compare
    (match-lambda
      ((vector id1 id2)
       (let ((t1 (string-append (name_of id1) (seg_of id1)))
             (t2 (string-append (name_of id2) (seg_of id2))))
         (string-compare t1 t2)))))
  
  (define fullname
    (match-lambda
      ((vector name thy)
       (stringquote (string-append thy "$" thy)))))
  
  (define (id_to_string p)
    (fullname (unbox p)))
  
  (define to_hol_type
    (match-lambda
      ((struct GRND (ty))
       ty)
      ((struct POLY (ty))
       ty)))
  
  )