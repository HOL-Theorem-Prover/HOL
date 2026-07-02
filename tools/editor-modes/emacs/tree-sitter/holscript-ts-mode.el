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
  '("Definition" "Theorem" "Triviality" "Termination" "Proof" "QED"
    "Datatype" "Inductive" "CoInductive"
    "Theory" "Ancestors" "Libs" "Overload" "Type" "Resume" "Finalise"
    "End"
    "if" "then" "else" "case" "of")
  "HOL keywords for tree-sitter font-locking.  These must be literal
anonymous nodes in the grammar; block keywords like `Quote' whose
whole span is a single lexical token are highlighted separately.")

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
       ;; A Definition body is now a bare `_hol_term' — the eqn shape
       ;; is a hol_binary_term with `=' as operator.  Font-locking the
       ;; function name requires a deep query and is deferred.
       ;; TODO: restore function-name highlighting.
       ((hol_alphanumeric) @font-lock-variable-name-face)))

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

(defconst holscript-ts-mode--defun-type-regexp
  (regexp-opt '("hol_theorem_with_proof"
                "hol_theorem_alias"
                "hol_definition"
                "hol_definition_with_proof"
                "hol_datatype"
                "hol_inductive"
                "hol_type_alias"
                "hol_overload"
                "hol_quote_block"
                "hol_theory_dec"
                "hol_ancestors_dec"
                "hol_libs_dec"
                "fun_dec"
                "val_dec"
                "type_dec"
                "datatype_dec"
                "exception_dec"
                "strbind"
                "sigbind"
                "fctbind"))
  "Regexp matching tree-sitter node types that `holscript-ts-mode'
treats as defuns for `C-M-a' / `C-M-e' / `narrow-to-defun' etc.")

(defun holscript-ts-mode--defun-name (node)
  "Return the user-visible name of NODE, or nil if NODE has none.
Used as `treesit-defun-name-function'."
  (pcase (treesit-node-type node)
    ((or "hol_theorem_with_proof" "hol_theorem_alias")
     (when-let ((n (treesit-search-subtree node "\\`hol_thmname\\'")))
       (treesit-node-text n t)))
    ((or "hol_definition" "hol_definition_with_proof" "hol_inductive")
     (when-let ((n (treesit-search-subtree node "\\`hol_defname\\'")))
       (treesit-node-text n t)))
    ("hol_type_alias"
     (when-let ((n (treesit-search-subtree node "\\`hol_typename\\'")))
       (treesit-node-text n t)))
    ("hol_overload"
     (when-let ((n (treesit-search-subtree node "\\`hol_overloadname\\'")))
       (treesit-node-text n t)))
    ("hol_theory_dec"
     (when-let ((n (treesit-search-subtree node "\\`hol_theoryname\\'")))
       (treesit-node-text n t)))
    ("hol_quote_block"
     ;; Single lexical token; name extracted from the head of the
     ;; token's text via regex.  Substring caps the regex input so
     ;; multi-kilobyte Quote bodies don't get scanned needlessly.
     (let ((text (buffer-substring-no-properties
                  (treesit-node-start node)
                  (min (treesit-node-end node)
                       (+ (treesit-node-start node) 256)))))
       (and (string-match "\\`Quote[ \t]+\\([A-Za-z][A-Za-z0-9_']*\\)" text)
            (match-string 1 text))))
    ("hol_datatype"
     ;; Datatype: foo = ... End — name is the first hol_identifier
     ;; inside the hol_binding child.
     (when-let* ((binding (treesit-search-subtree node "\\`hol_binding\\'"))
                 (ident (treesit-search-subtree binding "\\`hol_identifier\\'")))
       (treesit-node-text ident t)))
    ((or "valbind" "fmrule" "strbind" "sigbind" "fctbind")
     (when-let ((n (treesit-node-child-by-field-name node "name")))
       (treesit-node-text n t)))
    ("val_dec"
     ;; A val_dec wraps one or more valbinds; report the first pattern.
     (when-let* ((b (treesit-search-subtree node "\\`valbind\\'"))
                 (p (treesit-node-child-by-field-name b "pat")))
       (treesit-node-text p t)))
    ("fun_dec"
     (when-let* ((r (treesit-search-subtree node "\\`fmrule\\'"))
                 (n (treesit-node-child-by-field-name r "name")))
       (treesit-node-text n t)))
    ((or "type_dec" "datatype_dec" "exception_dec")
     ;; These wrap a typbind/datbind/exbind whose `name' field carries
     ;; the user-visible label.
     (when-let ((n (treesit-search-subtree node "\\`tycon\\'\\|\\`vid\\'")))
       (treesit-node-text n t)))))

(defconst holscript-ts-mode--imenu-settings
  `(("Theorem"    "\\`hol_theorem\\(_with_proof\\|_alias\\)\\'" nil nil)
    ("Definition" "\\`hol_definition\\(_with_proof\\)?\\'" nil nil)
    ("Inductive"  "\\`hol_inductive\\'"               nil nil)
    ("Datatype"   "\\`hol_datatype\\'"                nil nil)
    ("Type"       "\\`hol_type_alias\\'"              nil nil)
    ("Overload"   "\\`hol_overload\\'"                nil nil)
    ("Quote"      "\\`hol_quote_block\\'"             nil nil)
    ("Theory"     "\\`hol_theory_dec\\'"              nil nil)
    ("Function"   "\\`fun_dec\\'"                     nil nil)
    ("Value"      "\\`val_dec\\'"                     nil nil)
    ("Structure"  "\\`strbind\\'"                     nil nil)
    ("Signature"  "\\`sigbind\\'"                     nil nil)
    ("Functor"    "\\`fctbind\\'"                     nil nil))
  "Categories for `treesit-simple-imenu-settings'.")

(defconst holscript-ts-mode--block-keywords
  '("Theorem" "Triviality" "Proof" "QED"
    "Definition" "Inductive" "CoInductive" "Datatype"
    "End" "Termination"
    "Quote" "Theory" "Ancestors" "Libs"
    "Type" "Overload" "Resume" "Finalise")
  "HOL block keywords that always sit in column 0.")

(defconst holscript-ts-mode--indent-rules
  `((holscript
     ;; HOL block keywords always go to column 0 of the buffer.
     ((node-is ,(regexp-opt holscript-ts-mode--block-keywords))
      column-0 0)
     ;; The body of a HOL block (statement, tactic, definition spec,
     ;; datatype binding) indents 2 from the block's start column.
     ((parent-is "hol_theorem_with_proof")        parent-bol 2)
     ((parent-is "hol_theorem_alias")             parent-bol 2)
     ((parent-is "hol_definition")                parent-bol 2)
     ((parent-is "hol_definition_with_proof")     parent-bol 2)
     ((parent-is "hol_inductive")                 parent-bol 2)
     ((parent-is "hol_datatype")                  parent-bol 2)
     ((parent-is "hol_type_alias")                parent-bol 2)
     ((parent-is "hol_overload")                  parent-bol 2)
     ((parent-is "hol_theory_dec")                parent-bol 2)
     ((parent-is "hol_ancestors_dec")             parent-bol 2)
     ((parent-is "hol_libs_dec")                  parent-bol 2)
     ;; hol_quote_block is a single token with no inner structure;
     ;; treesit-indent won't recurse into it but if asked to indent
     ;; lines whose containing node IS the block, leave them alone.
     ((node-is "hol_quote_block")                 no-indent 0)
     ((parent-is "hol_quote_block")               no-indent 0)
     ;; Tactic chains: keep each tactic aligned with the first.
     ((parent-is "tactic")                        parent-bol 0)
     ;; SML let / in / end.
     ((node-is "in")                              parent-bol 0)
     ((node-is "end")                             parent-bol 0)
     ((parent-is "let_dec")                       parent-bol 2)
     ((parent-is "let_exp")                       parent-bol 2)
     ;; case / of: align match clauses with the case keyword.
     ((node-is "|")                               parent-bol 2)
     ((parent-is "case_exp")                      parent-bol 4)
     ;; if / then / else.
     ((node-is "then")                            parent-bol 0)
     ((node-is "else")                            parent-bol 0)
     ((parent-is "if_exp")                        parent-bol 4)
     ;; Don't auto-reindent inside HOL terms or quoted material;
     ;; leave the user's choices alone (the parser may not have full
     ;; precedence information yet — see grammar.js TODOs).
     ((parent-is "hol_term")                      no-indent 0)
     ((parent-is "hol_thmstmt")                   no-indent 0)
     ((parent-is "backquote")                     no-indent 0)
     ((parent-is "quoted_term")                   no-indent 0)
     ;; Inside ERROR regions, leave indent alone so the user can edit
     ;; without it jumping under them.
     ((node-is "ERROR")                           no-indent 0)
     ((parent-is "ERROR")                         no-indent 0)
     ;; Catch-all: leave the current indent unchanged.
     ((lambda (&rest _) t)                        no-indent 0))))

(defconst holscript-ts-mode--sexp-node-regexp
  (regexp-opt
   '("hol_theorem_with_proof"
     "hol_theorem_alias"
     "hol_definition"
     "hol_definition_with_proof"
     "hol_inductive"
     "hol_type_alias"
     "hol_datatype"
     "hol_overload"
     "hol_quote_block"
     "hol_theory_dec"
     "hol_ancestors_dec"
     "hol_libs_dec"
     "hol_term"
     "hol_application"
     "hol_binary_term"
     "hol_binder"
     "tuple_exp"
     "list_exp"
     "record_exp"
     "paren_exp"
     "let_exp"
     "case_exp"
     "fn_exp"
     "if_exp"
     "app_exp"
     "valbind"
     "fmrule"
     "tactic"
     "block_comment"
     "string_scon"
     "hol_string"))
  "Regexp matching node types treated as sexps by `forward-sexp'.")

(defconst holscript-ts-mode--sentence-node-regexp
  (regexp-opt
   '("hol_theorem_with_proof"
     "hol_theorem_alias"
     "hol_definition"
     "hol_definition_with_proof"
     "hol_inductive"
     "hol_type_alias"
     "hol_datatype"
     "hol_overload"
     "hol_quote_block"
     "hol_theory_dec"
     "hol_ancestors_dec"
     "hol_libs_dec"
     "val_dec" "fun_dec" "type_dec" "datatype_dec"
     "open_dec" "exception_dec"
     "strbind" "sigbind" "fctbind"))
  "Regexp matching node types treated as sentences by `forward-sentence'.")

(defconst holscript-ts-mode--thing-settings
  `((holscript
     (sexp ,holscript-ts-mode--sexp-node-regexp)
     (sentence ,holscript-ts-mode--sentence-node-regexp)))
  "Settings for `treesit-thing-settings' (sexp + sentence).")

;;;###autoload
(define-derived-mode holscript-ts-mode prog-mode "HOLScript[ts]"
  "Major mode for editing HOL Script.sml files with tree-sitter."
  :syntax-table holscript-ts-mode--syntax-table

  ;; Comments — same shape as `holscript-mode-variables' uses.
  (setq-local comment-start "(* "
              comment-end " *)"
              comment-start-skip "(\\*+\\s-*"
              comment-end-skip "\\s-*\\*+)"
              comment-quote-nested nil
              parse-sexp-ignore-comments t)
  (setq-local font-lock-multiline t)
  (setq-local indent-tabs-mode nil)

  (when (treesit-ready-p 'holscript)
    (treesit-parser-create 'holscript)

    ;; Font-Locking
    (setq-local treesit-font-lock-settings
                holscript-ts-mode--font-lock-settings)
    (setq-local treesit-font-lock-feature-list
                holscript-ts-mode--font-lock-feature-list)

    ;; Defun navigation
    (setq-local treesit-defun-type-regexp
                holscript-ts-mode--defun-type-regexp)
    (setq-local treesit-defun-name-function
                #'holscript-ts-mode--defun-name)

    ;; Imenu
    (setq-local treesit-simple-imenu-settings
                holscript-ts-mode--imenu-settings)

    ;; Sexp / sentence motion.  Emacs 30 reads `treesit-thing-settings';
    ;; Emacs 29 reads the per-thing regexp variables.  Set both, and
    ;; pin `forward-sexp-function' after setup because Emacs 29's
    ;; `treesit-major-mode-setup' does not always wire it.
    (setq-local treesit-thing-settings
                holscript-ts-mode--thing-settings)
    (when (boundp 'treesit-sexp-type-regexp)
      (setq-local treesit-sexp-type-regexp
                  holscript-ts-mode--sexp-node-regexp))
    (when (boundp 'treesit-sentence-type-regexp)
      (setq-local treesit-sentence-type-regexp
                  holscript-ts-mode--sentence-node-regexp))

    ;; Indent
    (setq-local treesit-simple-indent-rules
                holscript-ts-mode--indent-rules)

    (treesit-major-mode-setup)

    (when (fboundp 'treesit-forward-sexp)
      (setq-local forward-sexp-function #'treesit-forward-sexp))))

(provide 'holscript-ts-mode)
