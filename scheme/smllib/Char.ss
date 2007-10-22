(module Char (lib "ml.scm" "lang")
  (provide Char@)
  (require "Char-sig.ss"
           "Strbase.ss")
  (define-structure
    Char@
    Char^
    (define minChar #\nul)
    (define maxChar #\U0010FFFF)
    (define maxOrd #x10FFFF)
    (define ord char->integer)
    (define (chr i)
      (call-with-exception-handler
       (lambda (f) (struct Chr ()))
       (lambda () (integer->char i))))
    (define (succ c)
      (call-with-exception-handler
       (lambda (f) (struct Chr ()))
       (lambda ()
         (integer->char (add1 (char->integer c))))))
    (define (pred c)
      (call-with-exception-handler
       (lambda (f) (struct Chr ()))
       (lambda ()
         (integer->char (add1 (char->integer c))))))
    (define <
      (match-lambda
        ((list (cons '1 c1) (cons '2 c2))
         (char<? c1 c2))))
    (define <=
      (match-lambda
        ((list (cons '1 c1) (cons '2 c2))
         (char<=? c1 c2))))
    (define >
      (match-lambda
        ((list (cons '1 c1) (cons '2 c2))
         (char>? c1 c2))))
    (define >=
      (match-lambda
        ((list (cons '1 c1) (cons '2 c2))
         (char>=? c1 c2))))
    (define compare
      (match-lambda
        ((list (cons '1 c1) (cons '2 c2))
         (cond ((char<? c1 c2)
                (struct LESS ()))
               ((char=? c1 c2)
                (struct EQUAL ()))
               (else
                (struct GREATER ()))))))
    (define contains
      (lambda (s)
        (lambda (c)
          (and (memv c (string->list s)) #t))))
    (define notContains
      (lambda (s)
        (lambda (c)
          (not (memv c (string->list s))))))
    (define toLower char-downcase)
    (define toUpper char-upcase)
    (define isAlpha char-alphabetic?)
    (define (isAlphaNum c)
      (or (char-alphabetic? c)
          (char-numeric? c)))
    (define (isAscii c)
      (<= (char->integer c) 127))
    (define isCntrl char-iso-control?)
    (define isDigit char-numeric?)
    (define isGraph char-graphic?)
    (define (isHexDigit c)
      (or (char-numeric? c)
          (and (memv (char-downcase c) '(#\a #\b #\c #\d #\e #f)))))
    (define isLower char-lower-case?)
    (define (isPrint c)
      (not (char-iso-control? c)))
    (define isSpace char-blank?)
    (define isPunct char-punctuation?)
    (define isUpper char-upper-case?)
    (define toString (ml-dot Strbase@ toMLescape))
    (define
      fromString
      (lambda (s)
        (let ()
          (define getc
            (lambda (i)
              (if (< i (string-length s))
                  (struct SOME ((list (cons '1 (string-ref s i)) (cons '2 (+ i 1)))))
                  (struct NONE ()))))
          ((match-lambda
             ((struct NONE ()) (struct NONE ()))
             ((struct SOME ((list-no-order (cons '1 #\\) (cons '2 rest))))
              ((match-lambda
                 ((struct NONE ()) (struct NONE ()))
                 ((struct SOME ((list-no-order (cons '1 c) (cons '2 _))))
                  (struct SOME (c))))
               (((ml-dot Strbase@ fromMLescape) getc) rest)))
             ((struct SOME ((list-no-order (cons '1 c) (cons '2 _))))
              (struct SOME (c))))
           (getc 0)))))
    (define
      fromCString
      (lambda (s)
        (let ()
          (define getc
            (lambda (i)
              (if (< i (string-length s))
                  (struct SOME ((list (cons '1 (string-ref s i)) (cons '2 (+ i 1)))))
                  (struct NONE ()))))
          ((match-lambda
             ((struct NONE ()) (struct NONE ()))
             ((struct SOME ((list-no-order (cons '1 #\\) (cons '2 rest))))
              ((match-lambda
                 ((struct NONE ()) (struct NONE ()))
                 ((struct SOME ((list-no-order (cons '1 c) (cons '2 _))))
                  (struct SOME (c))))
               (((ml-dot Strbase@ fromCescape) getc) rest)))
             ((struct SOME ((list-no-order (cons '1 c) (cons '2 _))))
              (struct SOME (c))))
           (getc 0)))))
    (define toCString (ml-dot Strbase@ toCescape))))