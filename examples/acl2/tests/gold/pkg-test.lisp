(DEFPKG "MY-PKG" '(CONS DEFUN))

; NOTE: Forms below are not evaluated when translating to ML.
(IN-PACKAGE "MY-PKG")

(DEFUN MY-PKG::F1 (MY-PKG::X) (CONS MY-PKG::X MY-PKG::X))

(DEFUN MY-PKG::F2 (MY-PKG::X) (BINARY-APPEND MY-PKG::X MY-PKG::X))
