; This total order book, put together by Matt Kaufmann, is culled from events
; contributed by Pete Manolios and also benefits from contributions by Rob
; Sumners.

(in-package "ACL2")

(defun << (x y)
  (declare (xargs :guard t))
  (and (lexorder x y)
       (not (equal x y))))

(defthm <<-irreflexive
  (not (<< x x)))

(defthm <<-transitive
  (implies (and (<< x y)
                (<< y z))
           (<< x z)))

(defthm <<-asymmetric
  (implies (<< x y)
           (not (<< y x))))

(defthm <<-trichotomy
  (implies (and (not (<< y x))
                (not (equal x y)))
           (<< x y)))

(defthm <<-implies-lexorder
  (implies (<< x y)
	   (lexorder x y)))

(in-theory (disable <<))
