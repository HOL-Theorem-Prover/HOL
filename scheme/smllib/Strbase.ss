(module Strbase (lib "ml.scm" "lang")
  (provide Strbase@)
  (require "Strbase-sig.ss" "List.ss")
  (define-structure
   Strbase@
   Strbase^
   (define maxlen 16777211)
   (match-define
     (list
      foldl
      translate
      (list splitl splitr dropl dropr takel taker)
      tokens
      fields
      (list
       fromMLescape
       toMLescape
       toCescape
       |fromCescape'|
       fromCescape
       fromCString))
     (let ()
       (define str
         (lambda (c)
           (let ()
             (define newstr (make-string 1))
             (begin (string-set! newstr 0 c) newstr))))
       (define revconcat
         (lambda (strs)
           (let ()
             (define acc
               (lambda (_id10543)
                 (lambda (_id10544)
                   ((match-lambda
                      ((list-no-order (cons '1 (list)) (cons '2 len)) len)
                      ((list-no-order (cons '1 (cons v1 vr)) (cons '2 len))
                       ((acc vr) (+ (string-length v1) len))))
                    (list (cons '1 _id10543) (cons '2 _id10544))))))
             (define len ((acc strs) 0))
             (define newstr
               (if (> len maxlen) (raise (struct Size ())) (make-string len)))
             (define copyall
               (lambda (_id10545)
                 (lambda (_id10546)
                   ((match-lambda
                      ((list-no-order (cons '1 to) (cons '2 (list))) (list))
                      ((list-no-order (cons '1 to) (cons '2 (cons v1 vr)))
                       (let ()
                         (define len1 (string-length v1))
                         (define to (- to len1))
                         (begin
                           (string-copy! newstr to v1 0 len1)
                           ((copyall to) vr)))))
                    (list (cons '1 _id10545) (cons '2 _id10546))))))
             (begin ((copyall len) strs) newstr))))
       (define rest
         (match-lambda
           ((and ss (list-no-order (cons '1 s) (cons '2 i) (cons '3 n)))
            (if (eqv? n 0)
              ss
              (list (cons '1 s) (cons '2 (+ i 1)) (cons '3 (- n 1)))))))
       (list
        (lambda (f)
          (lambda (e)
            (match-lambda
              ((list-no-order (cons '1 s) (cons '2 i) (cons '3 n))
               (let ()
                 (define stop (+ i n))
                 (define h
                   (lambda (j)
                     (lambda (res)
                       (if (>= j stop)
                         res
                         ((h (+ j 1))
                          (f (list (cons '1 (string-ref s j)) (cons '2 res))))))))
                 ((h i) e))))))
        (lambda (f)
          (match-lambda
            ((list-no-order (cons '1 s) (cons '2 i) (cons '3 n))
             (let ()
               (define stop (+ i n))
               (define h
                 (lambda (j)
                   (lambda (res)
                     (if (>= j stop)
                       res
                       ((h (+ j 1)) (cons (f (string-ref s j)) res))))))
               (revconcat ((h i) (list)))))))
        (let ()
          (define scanl
            (lambda (chop)
              (lambda (pred)
                (match-lambda
                  ((list-no-order (cons '1 s) (cons '2 i) (cons '3 n))
                   (let ()
                     (define stop (+ i n))
                     (define scan
                       (lambda (j) (if (and (< j stop) #f) (scan (+ j 1)) j)))
                     (chop
                      (list
                       (cons '1 s)
                       (cons '2 i)
                       (cons '3 n)
                       (cons '4 (- (scan i) i))))))))))
          (define scanr
            (lambda (chop)
              (lambda (pred)
                (match-lambda
                  ((list-no-order (cons '1 s) (cons '2 i) (cons '3 n))
                   (let ()
                     (define stop (- i 1))
                     (define scan
                       (lambda (j) (if (and (> j stop) #f) (scan (- j 1)) j)))
                     (chop
                      (list
                       (cons '1 s)
                       (cons '2 i)
                       (cons '3 n)
                       (cons '4 (+ (- (scan (- (+ i n) 1)) i) 1))))))))))
          (list
           (scanl
            (match-lambda
              ((list-no-order (cons '1 s) (cons '2 i) (cons '3 n) (cons '4 k))
               (list
                (cons '1 (list (cons '1 s) (cons '2 i) (cons '3 k)))
                (cons
                 '2
                 (list (cons '1 s) (cons '2 (+ i k)) (cons '3 (- n k))))))))
           (scanr
            (match-lambda
              ((list-no-order (cons '1 s) (cons '2 i) (cons '3 n) (cons '4 k))
               (list
                (cons '1 (list (cons '1 s) (cons '2 i) (cons '3 k)))
                (cons
                 '2
                 (list (cons '1 s) (cons '2 (+ i k)) (cons '3 (- n k))))))))
           (scanl
            (match-lambda
              ((list-no-order (cons '1 s) (cons '2 i) (cons '3 n) (cons '4 k))
               (list (cons '1 s) (cons '2 (+ i k)) (cons '3 (- n k))))))
           (scanr
            (match-lambda
              ((list-no-order (cons '1 s) (cons '2 i) (cons '3 n) (cons '4 k))
               (list (cons '1 s) (cons '2 i) (cons '3 k)))))
           (scanl
            (match-lambda
              ((list-no-order (cons '1 s) (cons '2 i) (cons '3 n) (cons '4 k))
               (list (cons '1 s) (cons '2 i) (cons '3 k)))))
           (scanr
            (match-lambda
              ((list-no-order (cons '1 s) (cons '2 i) (cons '3 n) (cons '4 k))
               (list (cons '1 s) (cons '2 (+ i k)) (cons '3 (- n k))))))))
        (lambda (isDelim)
          (lambda (ss)
            (let ()
              (define findTok (dropl isDelim))
              (define h
                (match-lambda
                  ((and remains
                        (list-no-order (cons '1 _) (cons '2 _) (cons '3 n)))
                   (lambda (res)
                     (if (eqv? n 0)
                       ((ml-dot List@ rev) res)
                       (let ()
                         (match-define
                           (list-no-order (cons '1 token) (cons '2 aftertoken))
                           ((splitl (lambda (c) (not (isDelim c)))) remains))
                         ((h (findTok aftertoken)) (cons token res))))))))
              ((h (findTok ss)) (list)))))
        (lambda (isDelim)
          (lambda (ss)
            (let ()
              (define h
                (lambda (ss)
                  (lambda (res)
                    (let ()
                      (match-define
                        (list-no-order
                          (cons '1 field)
                          (cons
                           '2
                           (and afterfield
                                (list-no-order
                                  (cons '1 _)
                                  (cons '2 _)
                                  (cons '3 n)))))
                        ((splitl (lambda (c) (not (isDelim c)))) ss))
                      (if (eqv? n 0)
                        ((ml-dot List@ rev) (cons field res))
                        ((h (rest afterfield)) (cons field res)))))))
              ((h ss) (list)))))
        (let ()
          (define-struct BadEscape () #f)
          (define maxOrd 255)
          (define chr
            (lambda (i)
              (if (or (< i 0) (> i maxOrd))
                (raise (struct BadEscape ()))
                (integer->char i))))
          (define decval (lambda (c) (- (char->integer c) 48)))
          (define digit (lambda (n) (integer->char (+ 48 n))))
          (define hexval
            (lambda (c)
              (if (and (<= #\0 c) #f)
                (- (char->integer c) 48)
                (modulo (- (char->integer c) 55) 32))))
          (define isOctDigit (lambda (c) (and (<= #\0 c) #f)))
          (define isHexDigit
            (lambda (c)
              (or (and (<= #\0 c) #f)
                  (and (<= #\a c) #f)
                  (and (<= #\A c) #f))))
          (list
           (lambda (getc)
             (lambda (source)
               (let ()
                 (define decimal
                   (lambda (cont)
                     (lambda (src)
                       (lambda (code)
                         ((match-lambda
                            ((struct NONE ()) (raise (struct BadEscape ())))
                            ((struct
                               SOME
                               ((list-no-order (cons '1 c) (cons '2 rest))))
                             (if (and (<= #\0 c) #f)
                               ((cont rest) (- (+ (* code 10) (char->integer c)) 48))
                               (raise (struct BadEscape ())))))
                          (getc src))))))
                 (define from3Dec
                   (decimal
                     (decimal
                       (decimal
                         (lambda (src)
                           (lambda (code)
                             (list
                              (cons '1 (integer->char code))
                              (cons '2 src))))))))
                 (define skipform
                   (lambda (src)
                     ((match-lambda
                        ((struct NONE ()) (struct NONE ()))
                        ((struct
                           SOME
                           ((list-no-order (cons '1 #\\) (cons '2 src1))))
                         ((match-lambda
                            ((struct NONE ()) (struct NONE ()))
                            ((struct
                               SOME
                               ((list-no-order (cons '1 #\\) (cons '2 src2))))
                             ((fromMLescape getc) src2))
                            (res res))
                          (getc src1)))
                        ((struct
                           SOME
                           ((list-no-order (cons '1 c) (cons '2 rest))))
                         (if (or (eqv? c #\space) (and (<= #\tab c) #f))
                           (skipform rest)
                           (struct NONE ()))))
                      (getc src))))
                 ((match-lambda
                    ((struct NONE ()) (struct NONE ()))
                    ((struct
                       SOME
                       ((list-no-order (cons '1 #\a) (cons '2 rest))))
                     (struct SOME ((list (cons '1 #\u0007) (cons '2 rest)))))
                    ((struct
                       SOME
                       ((list-no-order (cons '1 #\b) (cons '2 rest))))
                     (struct
                       SOME
                       ((list (cons '1 #\backspace) (cons '2 rest)))))
                    ((struct
                       SOME
                       ((list-no-order (cons '1 #\t) (cons '2 rest))))
                     (struct SOME ((list (cons '1 #\tab) (cons '2 rest)))))
                    ((struct
                       SOME
                       ((list-no-order (cons '1 #\n) (cons '2 rest))))
                     (struct SOME ((list (cons '1 #\newline) (cons '2 rest)))))
                    ((struct
                       SOME
                       ((list-no-order (cons '1 #\r) (cons '2 rest))))
                     (struct SOME ((list (cons '1 #\return) (cons '2 rest)))))
                    ((struct
                       SOME
                       ((list-no-order (cons '1 #\v) (cons '2 rest))))
                     (struct SOME ((list (cons '1 #\vtab) (cons '2 rest)))))
                    ((struct
                       SOME
                       ((list-no-order (cons '1 #\f) (cons '2 rest))))
                     (struct SOME ((list (cons '1 #\page) (cons '2 rest)))))
                    ((struct
                       SOME
                       ((list-no-order (cons '1 #\") (cons '2 rest))))
                     (struct SOME ((list (cons '1 #\") (cons '2 rest)))))
                    ((struct
                       SOME
                       ((list-no-order (cons '1 #\\) (cons '2 rest))))
                     (struct SOME ((list (cons '1 #\\) (cons '2 rest)))))
                    ((struct
                       SOME
                       ((list-no-order (cons '1 #\space) (cons '2 rest))))
                     (skipform rest))
                    ((struct
                       SOME
                       ((list-no-order (cons '1 #\newline) (cons '2 rest))))
                     (skipform rest))
                    ((struct
                       SOME
                       ((list-no-order (cons '1 #\tab) (cons '2 rest))))
                     (skipform rest))
                    ((struct
                       SOME
                       ((list-no-order (cons '1 #\^) (cons '2 rest))))
                     ((match-lambda
                        ((struct NONE ()) (struct NONE ()))
                        ((struct
                           SOME
                           ((list-no-order (cons '1 c) (cons '2 rest))))
                         (if (and (<= #\@ c) #f)
                           (struct
                             SOME
                             ((list
                               (cons '1 (integer->char (- (char->integer c) 64)))
                               (cons '2 rest))))
                           (struct NONE ()))))
                      (getc rest)))
                    (_
                     (with-handlers
                       (((match-lambda ((struct BadEscape ()) #t))
                         (match-lambda
                           ((struct BadEscape ()) (struct NONE ())))))
                       (struct SOME (((from3Dec source) 0))))))
                  (getc source)))))
           (match-lambda
             (#\\ "\\\\")
             (#\" "\\\"")
             (c
              (if (<= #\space c)
                (if (<= c #\~)
                  (char->string c)
                  (let ()
                    (define n (char->integer c))
                    (define newstr (make-string 4))
                    (begin
                      (string-set! newstr 0 #\\)
                      (string-set! newstr 1 (digit (/ n 100)))
                      (string-set! newstr 2 (digit (modulo (/ n 10) 10)))
                      (string-set! newstr 3 (digit (modulo n 10)))
                      newstr)))
                ((match-lambda
                   (#\u0007 "\\a")
                   (#\backspace "\\b")
                   (#\tab "\\t")
                   (#\newline "\\n")
                   (#\return "\\r")
                   (#\vtab "\\v")
                   (#\page "\\f")
                   (_
                    (let ()
                      (define n (char->integer c))
                      (define newstr (make-string 3))
                      (begin
                        (string-set! newstr 0 #\\)
                        (string-set! newstr 1 #\^)
                        (string-set! newstr 2 (integer->char (+ (char->integer c) 64)))
                        newstr))))
                 c))))
           (match-lambda
             (#\\ "\\\\")
             (#\? "\\?")
             (#\| "\\|'|")
             (#\" "\\\"")
             (c
              (if (and (<= #\space c) #f)
                (char->string c)
                ((match-lambda
                   (#\newline "\\n")
                   (#\return "\\r")
                   (#\tab "\\t")
                   (#\vtab "\\v")
                   (#\backspace "\\b")
                   (#\page "\\f")
                   (#\u0007 "\\a")
                   (_
                    (let ()
                      (define n (char->integer c))
                      (define newstr (make-string 4))
                      (begin
                        (string-set! newstr 0 #\\)
                        (string-set! newstr 1 (digit (/ n 64)))
                        (string-set! newstr 2 (digit (modulo (/ n 8) 8)))
                        (string-set! newstr 3 (digit (modulo n 8)))
                        newstr))))
                 c))))
           (lambda (getc)
             (lambda (src)
               (let ()
                 (define fromHex
                   (lambda (src)
                     (lambda (code)
                       ((match-lambda
                          ((struct NONE ())
                           (list (cons '1 (integer->char code)) (cons '2 src)))
                          ((struct
                             SOME
                             ((list-no-order (cons '1 c) (cons '2 rest))))
                           (if (isHexDigit c)
                             ((fromHex rest) (+ (* code 16) (hexval c)))
                             (list
                              (cons '1 (integer->char code))
                              (cons '2 src)))))
                        (getc src)))))
                 (define octalOpt
                   (lambda (cont)
                     (lambda (src)
                       (lambda (code)
                         ((match-lambda
                            ((struct NONE ())
                             (list
                              (cons '1 (integer->char code))
                              (cons '2 src)))
                            ((struct
                               SOME
                               ((list-no-order (cons '1 c) (cons '2 rest))))
                             (if (and (<= #\0 c) #f)
                               ((cont rest) (- (+ (* code 8) (char->integer c)) 48))
                               (list
                                (cons '1 (integer->char code))
                                (cons '2 src)))))
                          (getc src))))))
                 (define fromOct
                   (octalOpt
                     (octalOpt
                       (lambda (src)
                         (lambda (code)
                           (list
                            (cons '1 (integer->char code))
                            (cons '2 src)))))))
                 ((match-lambda
                    ((struct NONE ()) (raise (struct BadEscape ())))
                    ((struct
                       SOME
                       ((list-no-order (cons '1 #\n) (cons '2 src1))))
                     (list (cons '1 #\newline) (cons '2 src1)))
                    ((struct
                       SOME
                       ((list-no-order (cons '1 #\r) (cons '2 src1))))
                     (list (cons '1 #\return) (cons '2 src1)))
                    ((struct
                       SOME
                       ((list-no-order (cons '1 #\t) (cons '2 src1))))
                     (list (cons '1 #\tab) (cons '2 src1)))
                    ((struct
                       SOME
                       ((list-no-order (cons '1 #\v) (cons '2 src1))))
                     (list (cons '1 #\vtab) (cons '2 src1)))
                    ((struct
                       SOME
                       ((list-no-order (cons '1 #\b) (cons '2 src1))))
                     (list (cons '1 #\backspace) (cons '2 src1)))
                    ((struct
                       SOME
                       ((list-no-order (cons '1 #\f) (cons '2 src1))))
                     (list (cons '1 #\page) (cons '2 src1)))
                    ((struct
                       SOME
                       ((list-no-order (cons '1 #\a) (cons '2 src1))))
                     (list (cons '1 #\u0007) (cons '2 src1)))
                    ((struct
                       SOME
                       ((list-no-order (cons '1 #\\) (cons '2 src1))))
                     (list (cons '1 #\\) (cons '2 src1)))
                    ((struct
                       SOME
                       ((list-no-order (cons '1 #\?) (cons '2 src1))))
                     (list (cons '1 #\?) (cons '2 src1)))
                    ((struct
                       SOME
                       ((list-no-order (cons '1 #\|) (cons '2 src1))))
                     (list (cons '1 #\|) (cons '2 src1)))
                    ((struct
                       SOME
                       ((list-no-order (cons '1 #\") (cons '2 src1))))
                     (list (cons '1 #\") (cons '2 src1)))
                    ((struct
                       SOME
                       ((list-no-order (cons '1 #\x) (cons '2 src1))))
                     ((match-lambda
                        ((struct NONE ()) (raise (struct BadEscape ())))
                        ((struct
                           SOME
                           ((list-no-order (cons '1 c) (cons '2 src2))))
                         (if (isHexDigit c)
                           ((fromHex src2) (hexval c))
                           (raise (struct BadEscape ())))))
                      (getc src1)))
                    ((struct SOME ((list-no-order (cons '1 c) (cons '2 src1))))
                     (if (isOctDigit c)
                       ((fromOct src1) (decval c))
                       (raise (struct BadEscape ())))))
                  (getc src)))))
           (lambda (getc)
             (lambda (src)
               (with-handlers
                 (((match-lambda ((struct BadEscape ()) #t))
                   (match-lambda ((struct BadEscape ()) (struct NONE ()))))
                  ((match-lambda ((struct Overflow ()) #t))
                   (match-lambda ((struct Overflow ()) (struct NONE ())))))
                 (struct SOME (((|fromCescape'| getc) src))))))
           (lambda (s)
             (let ()
               (define getc
                 (lambda (i)
                   (if (< i (string-length s))
                     (struct
                       SOME
                       ((list (cons '1 (string-ref s i)) (cons '2 (+ i 1)))))
                     (struct NONE ()))))
               (define max (box 1))
               (define tmp (box (make-string (unbox max))))
               (define realloc
                 (match-lambda
                   ((list-no-order)
                    (let ()
                      (define newmax (* 2 (unbox max)))
                      (define newtmp (make-string newmax))
                      (begin
                        (string-copy! newtmp 0 (unbox tmp) 0 (unbox max))
                        (set-box! max newmax)
                        (set-box! tmp newtmp))))))
               (define sub_string_
                 (lambda (s)
                   (lambda (start)
                     (lambda (len)
                       (let ()
                         (define res (make-string len))
                         (begin (string-copy! res 0 s start len) res))))))
               (define h
                 (lambda (len)
                   (lambda (src)
                     (let ()
                       (define addchar
                         (lambda (c)
                           (begin
                             (if (>= len (unbox max)) (realloc (list)) (list))
                             (string-set! (unbox tmp) len c))))
                       ((match-lambda
                          ((struct NONE ())
                           (((sub_string_ (unbox tmp)) 0) len))
                          ((struct
                             SOME
                             ((list-no-order (cons '1 #\\) (cons '2 src1))))
                           (let ()
                             (match-define
                               (list-no-order (cons '1 c) (cons '2 src2))
                               ((|fromCescape'| getc) src1))
                             (begin (addchar c) ((h (+ len 1)) src2))))
                          ((struct
                             SOME
                             ((list-no-order (cons '1 c) (cons '2 src1))))
                           (begin (addchar c) ((h (+ len 1)) src1))))
                        (getc src))))))
               (with-handlers
                 (((match-lambda ((struct BadEscape ()) #t))
                   (match-lambda ((struct BadEscape ()) (struct NONE ()))))
                  ((match-lambda ((struct Overflow ()) #t))
                   (match-lambda ((struct Overflow ()) (struct NONE ())))))
                 (struct SOME (((h 0) 0)))))))))))))
