; NOTE: Forms below are not evaluated when translating to ML.
(IN-PACKAGE "ACL2")

(DEFUN << (X Y) (IF (LEXORDER X Y) (NOT (EQUAL X Y)) 'NIL))

(DEFTHM <<-IRREFLEXIVE (NOT (<< X X)))

(DEFTHM <<-TRANSITIVE (IMPLIES (IF (<< X Y) (<< Y Z) 'NIL) (<< X Z)))

(DEFTHM <<-ASYMMETRIC (IMPLIES (<< X Y) (NOT (<< Y X))))

(DEFTHM <<-TRICHOTOMY
        (IMPLIES (IF (NOT (<< Y X))
                     (NOT (EQUAL X Y))
                     'NIL)
                 (<< X Y)))

(DEFTHM <<-IMPLIES-LEXORDER (IMPLIES (<< X Y) (LEXORDER X Y)))
