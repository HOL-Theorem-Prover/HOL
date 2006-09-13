(module locn mzscheme
  
  (require (lib "plt-match.ss"))
  
  (provide (all-defined))
  
  (define-struct LocP (nf r c) #f)
  (define-struct LocA (r c) #f)
  (define-struct LocPBeg (nf) #f)
  (define-struct LocPEnd (nf) #f)
  
  (define locn_point_toString
    (match-lambda
      ((struct LocP (nf r c))
       (string-append "frag "
                      (number->string nf)
                      " row "
                      (number->string r)
                      " col "
                      (number->string c)))
      ((struct LocA (r c))
       (string-append "line "
                      (number->string (+ r 1))
                      ", character "
                      (number->string (+ c 1))))
      ((struct LocPBeg (nf))
       (string-append "beginning of frag "
                      (number->string nf)))
      ((struct LocPEnd (nf))
       (string-append "end of frag "
                      (number->string nf)))))
  
  (define rel_to_abs
    (match-lambda*
      ((list row col (struct LocP (nf r c)))
       (if (= r 0)
           (make-LocA row (+ col c))))
      ((list row col locp)
       locp)))
  
  (define-struct Loc (locn_point1 locn_point2) #f)
  (define-struct Loc_Near (locn) #f)
  
  (define toString
    (match-lambda
      ((struct Loc ((struct LocP (nf1 r1 c1))
                    (struct LocP (nf2 r2 c2))))
       (cond ((not (= nf1 nf2))
              (string-append "between frag "
                             (number->string nf1)
                             " row "
                             (number->string r1)
                             " col "
                             (number->string c1)
                             " and frag "
                             (number->string nf2)
                             " row "
                             (number->string r2)
                             " col "
                             (number->string c2)))
             ((not (= r1 r2))
              (string-append "in frag "
                             (number->string nf1)
                             ", between row "
                             (number->string r1)
                             " col "
                             (number->string c1)
                             " and row "
                             (number->string r2)
                             " col "
                             (number->string c2)))
             ((not (= c1 c2))
              (string-append "on frag "
                             (number->string nf1)
                             " row "
                             (number->string r1)
                             ", between cols "
                             (number->string c1)
                             " and "
                             (number->string c2)))
             (else
              (string-append "at frag "
                             (number->string nf1)
                             " row "
                             (number->string r1)
                             " col "
                             (number->string c1)))))
      ((struct Loc ((struct LocA (r1 c1))
                    (struct LocA (r2 c2))))
       (cond ((not (= r1 r2))
              (string-append "between line "
                             (number->string (add1 r1))
                             ", character "
                             (number->string (add1 c1))
                             " and line "
                             (number->string (add1 r2))
                             ", character "
                             (number->string (add1 c2))))
             ((not (= c1 c2))
              (string-append "on line "
                             (number->string (add1 r1))
                             ", characters "
                             (number->string (add1 c1))
                             "-"
                             (number->string (add1 c2))))
             (else
              (string-append "at line "
                             (number->string (add1 r1))
                             ", character "
                             (number->string (add1 c1))))))
      ((struct Loc (s e))
       (if (equal? s e)
           (string-append "at "
                          (locn_point_toString s))
           (string-append "between "
                          (locn_point_toString s)
                          " and "
                          (locn_point_toString e))))
      ('Loc_None
        "in compiler-generated text")
      ('Loc_Unknown
        "in unknown location")
      ((struct Loc_Near (locn))
       (string-append "roughly "
                      (toString locn)))))
  
  (define (locp p)
    (make-Loc p p))
  
  (define (locfrag nf)
    (make-Loc (make-LocPBeg nf)
              (make-LocPEnd nf)))
  
  (define move_start
    (match-lambda*
      ((list delta
             (struct Loc ((struct LocP (nf r c)) e)))
       (make-Loc (make-LocP nf r (+ c delta)) e))
      ((list delta
             (struct Loc ((struct LocA (r c)) e)))
       (make-Loc (make-LocA r (+ c delta)) e))
      ((list delta locn)
       locn)))
  
  (define split_at
    (match-lambda*
      ((list delta
             (struct Loc ((struct LocP (nf r c)) e)))
       (vector (make-Loc (make-LocP nf r c)
                         (make-LocP nf r (+ c delta -1)))
               (make-Loc (make-LocP nf r (+ c delta))
                         e)))
      ((list delta
             (struct Loc ((struct LocA (r c)) e)))
       (vector (make-Loc (make-LocA r c)
                         (make-LocA r (+ c delta -1)))
               (make-Loc (make-LocA r (+ c delta))
                         e)))
      ((list delta locn)
       (vector locn locn))))
  
  (define (near l)
    (if (Loc_Near? l)
        l
        (make-Loc_Near l)))
  
  (define between
    (match-lambda*
      ((list (struct Loc (lploc _))
             (struct Loc (_ rploc)))
       (make-Loc lploc rploc))
      ((list 'Loc_None rloc)
       rloc)
      ((list lloc 'Loc_None)
       lloc)
      ((list 'Loc_Unknown rloc)
       (near rloc))
      ((list lloc 'Loc_Unknown)
       (near lloc))
      ((list (struct Loc_Near (lloc)) rloc)
       (near (between lloc rloc)))
      ((list lloc (struct Loc_Near (rloc)))
       (near (between lloc rloc)))))
  
  )