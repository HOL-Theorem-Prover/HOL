(require 'treesit)

;; References
;; * https://github.com/nverno/sml-ts-mode
;; * https://github.com/HOL-Theorem-Prover/HOL (holscript-mode.el)
;; * https://www.masteringemacs.org/article/lets-write-a-treesitter-major-mode

(defvar holscript-ts-mode--syntax-table
  (let ((st (make-syntax-table)))
    (modify-syntax-entry ?\* ". 23n" st)
    (modify-syntax-entry ?\( "()1" st)
    (modify-syntax-entry ?\) ")(4" st)
    (modify-syntax-entry ?“ "(”" st)
    (modify-syntax-entry ?” ")“" st)
    (modify-syntax-entry ?‘ "(’" st)
    (modify-syntax-entry ?’ ")‘" st)
    (modify-syntax-entry ?\\ "\\" st)
    (modify-syntax-entry ?λ "." st)
    ;; backslash only escapes in strings but we need to have it seen
    ;; as one in general if the hol-mode isn't to get seriously
    ;; confused by script files that contain escaped quotation
    ;; characters. This despite the fact that it does cause pain in
    ;; terms such as \(x,y). x + y
    (mapc (lambda (c) (modify-syntax-entry c "w" st)) "'")
    (mapc (lambda (c) (modify-syntax-entry c "_" st)) "$_")
    (mapc (lambda (c) (modify-syntax-entry c "."  st)) ".%&+-/:<=>?@`^|!~#,;∀∃")
    st)
  "Syntax table used in `holscript-ts-mode'.")

(defconst holscript-ts-mode--sml-keywords
  '(;; Reserved Words Core
    "abstype" "and" "andalso" "as" "case" "datatype" "do" "else" "end"
    "exception" "fn" "fun" "handle" "if" "in" "infix" "infixr" "let"
    "local" "nonfix" "of" "op" "open" "orelse" "raise" "rec" "then"
    "type" "val" "with" "withtype" "while"
    ;; Reserved Words Modules
    "eqtype" "functor" "include" "sharing" "sig" "signature" "struct"
    "structure" "where")
  "SML keywords for tree-sitter font-locking.")

(defconst holscript-ts-mode--hol-keywords
  '("Definition" "Theorem" "Termination" "Proof" "Datatype:" "End" "QED"
    "if" "then" "else" "case" "of")
  "HOL keywords for tree-sitter font-locking.")

(defconst holscript-ts-mode--sml-builtins
  '("abs" "app" "before" "ceil" "chr" "concat" "exnMessage" "exnName" "explode"
    "floor" "foldl" "foldr" "getOpt" "hd" "ignore" "implode" "isSome" "length"
    "map" "null" "ord" "print" "real" "rev" "round" "size" "str" "substring"
    "tl" "trunc" "valOf" "vector")
  "SML builtin functions for tree-sitter font-locking.")

(defvar holscript-ts-mode--font-lock-feature-list
  '((comment definition)
    (keyword string)
    (builtin constant number type property)
    (assignment bracket delimiter operator))
  "Font-lock features for `treesit-font-lock-feature-list' in `holscript-ts-mode'.")

(defun holscript-ts-mode--fontify-patterns (node override start end &rest _args)
  "Fontify pattern bindings and in NODE.
For a description of OVERRIDE, START, and END, see `treesit-font-lock-rules'."
  (pcase (treesit-node-type node)
    ((or "typed_pat" "paren_pat" "tuple_pat" "conj_pat")
     (holscript-ts-mode--fontify-patterns
      (treesit-node-child node 0 t) override start end))
    ("app_pat"
     ;; Fontify both bindings in (h::t)
     (when (equal "::" (treesit-node-text (treesit-node-child node 1)))
       (holscript-ts-mode--fontify-patterns
        (treesit-node-child node 0 t) override start end))
     (holscript-ts-mode--fontify-patterns
      (treesit-node-child node 1 t) override start end))
    ((or "vid_pat" "wildcard_pat")
     (treesit-fontify-with-override
      (treesit-node-start node) (treesit-node-end node)
      'font-lock-variable-name-face
      override start end))))

(defvar holscript-ts-mode--font-lock-settings
  (treesit-font-lock-rules
   :language 'holscript
   :feature 'comment ; SML and HOL
   '((block_comment) @font-lock-comment-face)

   :language 'holscript
   :feature 'string
   '(;; SML
     (string_scon) @font-lock-string-face
     (char_scon) @font-lock-constant-face
     ;; HOL
     (hol_string) @font-lock-string-face
     (hol_character) @font-lock-constant-face)

   :language 'holscript
   :feature 'keyword
   `(;; SML
     [,@holscript-ts-mode--sml-keywords] @font-lock-keyword-face
     ;; Misinterpreted identifiers, eg. val x = struct
     ;; See notes from highlights.scm (MatthewFluet/tree-sitter-sml)
     ([(vid) (tycon) (strid) (sigid) (fctid)] @font-lock-warning-face
      (:match ,(rx-to-string `(seq bos (or ,@holscript-ts-mode--sml-keywords) eos))
              @font-lock-warning-face))
     ;; As an additional special case, The Defn of SML excludes `*` from tycon.
     ([(tycon)] @font-lock-warning-face
      (:match ,(rx bos "*" eos) @font-lock-warning-face))
     ;; HOL
     [,@holscript-ts-mode--hol-keywords] @font-lock-keyword-face)

   :language 'holscript
   :feature 'builtin
   `(;; SML
     ((vid_exp) @font-lock-builtin-face
      (:match ,(rx-to-string `(seq bos (or ,@holscript-ts-mode--sml-builtins) eos))
              @font-lock-builtin-face))
     ((vid_exp) @font-lock-preprocessor-face
      (:match ,(rx bos (or "use") eos) @font-lock-preprocessor-face)))

   :language 'holscript
   :feature 'definition
   (let ((pats '((app_pat) (paren_pat) (vid_pat) (tuple_pat) (wildcard_pat))))
     `(;; SML
       (fmrule
        name: (_) @font-lock-function-name-face
        ([,@pats] :* @holscript-ts-mode--fontify-patterns :anchor "=") :?)
       (mrule ([,@pats] :* @holscript-ts-mode--fontify-patterns :anchor "=>"))
       (handle_exp (mrule (_) @holscript-ts-mode--fontify-patterns))
       (labvar_patrow [(vid)] @font-lock-variable-name-face)
       (patrow (vid_pat) @holscript-ts-mode--fontify-patterns)
       (tuple_pat (_) @holscript-ts-mode--fontify-patterns
                  ("," (vid_pat) @holscript-ts-mode--fontify-patterns) :*)
       (app_pat (_) (_) @holscript-ts-mode--fontify-patterns)
       (valbind pat: (_) @holscript-ts-mode--fontify-patterns)
       (valdesc name: (vid) @font-lock-variable-name-face)
       ;; Modules, Sigs
       (fctbind name: (_) @font-lock-module-def-face
                arg: (strid) :? @font-lock-variable-name-face)
       (strbind name: (_) @font-lock-module-def-face)
       (sigbind name: (_) @font-lock-module-def-face)
       ;; Types
       (datatype_dec (datbind name: (tycon) @font-lock-type-def-face))
       (datatype_spec (datdesc name: (tycon) @font-lock-type-def-face))
       (datatype_dec
        withtype: (typbind name: (tycon) @font-lock-type-def-face))
       (type_dec (typbind name: (tycon) @font-lock-type-def-face))
       (type_spec (typbind name: (tycon) @font-lock-type-def-face))
       (typedesc name: (_) @font-lock-type-def-face)
       (infix_dec (vid) @font-lock-function-name-face)
       ;; Uppercase does not mean we have a type
       ;; ((vid) @font-lock-type-face
       ;;  (:match "^[A-Z].*" @font-lock-type-face))
       ;; HOL
       ((hol_defname) @font-lock-variable-name-face)
       (hol_eqn (hol_identifier) @font-lock-function-name-face)
       ((hol_variable) @font-lock-variable-name-face)))

   :language 'holscript
   :feature 'constant
   `(;; SML
     ((vid) @font-lock-constant-face
      (:match ,(rx bos (or "true" "false" "nil" "ref") eos)
              @font-lock-constant-face))
     (recordsel_exp ((lab) @font-lock-constant-face
                     (:match "^[0-9]+$" @font-lock-constant-face))))

   :language 'holscript
   :feature 'property  ; SML only?
   `((tyrow (lab) @font-lock-property-name-face)
     (patrow (lab) @font-lock-property-use-face)
     (exprow (lab) @font-lock-property-use-face))

   :language 'holscript
   :feature 'type
   `(;; SML
     (fn_ty "->" @font-lock-type-face)
     (tuple_ty "*" @font-lock-type-face)
     (paren_ty ["(" ")"] @font-lock-type-face)
     (tyvar) @font-lock-type-face
     [(strid) (sigid) (fctid)] @font-lock-type-face
     (record_ty ["{" "," "}"] @font-lock-type-face
                (tyrow [(lab) ":"] @font-lock-type-face) :?
                (ellipsis_tyrow ["..." ":"] @font-lock-type-face) :?)
     (tycon_ty (tyseq ["(" "," ")"] @font-lock-type-face) :?
               (longtycon) @font-lock-type-face)
     ;; HOL
     ([(hol_atomic_type) (hol_list_ty) (hol_fun_ty)] @font-lock-type-face))

   :language 'holscript
   :feature 'number
   '(;; SML
     [(integer_scon) (word_scon) (real_scon)] @font-lock-number-face)))

;;;###autoload
(define-derived-mode holscript-ts-mode prog-mode "HOLScript[ts]"
  "Major mode for editing HOL Script.sml files with tree-sitter."
  :syntax-table holscript-ts-mode--syntax-table

  (when (treesit-ready-p 'holscript)
    (treesit-parser-create 'holscript)

    ;; Font-Locking
    (setq-local treesit-font-lock-settings
                holscript-ts-mode--font-lock-settings)
    (setq-local treesit-font-lock-feature-list
                holscript-ts-mode--font-lock-feature-list)

    (treesit-major-mode-setup)))

(provide 'holscript-ts-mode)
