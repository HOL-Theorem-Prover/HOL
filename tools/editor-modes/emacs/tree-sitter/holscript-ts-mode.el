(require 'treesit)
(require 'elec-pair)

;; `hol-input.el' and `holscript-mode.el' live in the parent
;; directory of this file; put that on `load-path' too so we can
;; find them when ts-mode is loaded standalone (the pick-mode
;; dispatcher already handles the load-path when ts-mode is loaded
;; via `holscript-pick-mode').
(eval-and-compile
  (when load-file-name
    (let ((parent (file-name-directory
                   (directory-file-name
                    (file-name-directory load-file-name)))))
      (when (file-directory-p parent)
        (add-to-list 'load-path parent)))))

;; `hol-input' registers the "Hol" Quail input method used for
;; ASCII-to-Unicode substitutions (`\<=>' → `⇔' etc.).  Same import
;; and behaviour as the SMIE-based `holscript-mode'.
(require 'hol-input)
;; `holscript-dbl-backquote' is defined in the SMIE-based mode file
;; and reused here.  Autoload it so ts-mode can be loaded on its
;; own without pulling all of `holscript-mode' up-front — the SMIE
;; mode file will be lazy-loaded the first time the key fires.
(autoload 'holscript-dbl-backquote "holscript-mode" nil t)

;; References
;; * https://github.com/nverno/sml-ts-mode
;; * https://github.com/HOL-Theorem-Prover/HOL (holscript-mode.el)
;; * https://www.masteringemacs.org/article/lets-write-a-treesitter-major-mode

;; --- Faces ---------------------------------------------------------
;; Mirror the palette from the SMIE-based `holscript-mode' so the
;; two modes look the same.  `defface' is a no-op when the face is
;; already defined with the same spec, so duplication is safe.

(defface holscript-theorem-syntax
  '((((class color)) :foreground "blueviolet"))
  "Face for Theorem/Proof/QED and related block-delimiter keywords."
  :group 'holscript-faces)

(defface holscript-thmname-syntax
  '((((class color)) :weight bold))
  "Face for theorem, definition, and datatype names."
  :group 'holscript-faces)

(defface holscript-cheat-face
  '((((class color)) :foreground "orange" :weight ultra-bold :box t))
  "Face for occurrences of the `cheat' tactic."
  :group 'holscript-faces)

(defface holscript-definition-syntax
  '((((class color)) :foreground "indianred"))
  "Face for Definition/End/Datatype and related block-delimiter keywords."
  :group 'holscript-faces)

(defface holscript-quoted-material
  '((((class color)) :foreground "brown" :weight bold))
  "Face for HOL quoted material (theorem statements, definition bodies,
term quotations)."
  :group 'holscript-faces)

(defface holscript-then-syntax
  '((((class color)) :foreground "DarkSlateGray4" :weight bold))
  "Face for `THEN' and other tactic combinators."
  :group 'holscript-faces)

(defface holscript-smlsyntax
  '((((class color)) :foreground "DarkOliveGreen" :weight bold))
  "Face for SML keywords that appear in script files."
  :group 'holscript-faces)

(defface holscript-definition-label-face
  '((((class color))
     :foreground "PaleVioletRed4"
     :box (:line-width 1 :color "PaleVioletRed4" :style released-button)
     :slant normal :weight light))
  "Face for `[~label:]' inside inductive/definition clauses."
  :group 'holscript-faces)

(defface holscript-hol-keyword
  '((((class color)) :foreground "brown" :weight bold :slant italic))
  "Face for HOL-context keywords (`if', `then', `else', `case', `of',
`let', `in', `with', ...).  A variant of `holscript-quoted-material'
with an italic slant so keywords stand out from surrounding HOL
identifiers while staying in the same colour family."
  :group 'holscript-faces)

(defface holscript-syntax-error-face
  '((((class color)) :foreground "red" :background "yellow"
     :weight bold :box t))
  "Face for likely syntax errors (e.g. two adjacent tactic
combinators like `THEN THEN')."
  :group 'holscript-faces)

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

(defconst holscript-ts-mode--theorem-block-keywords
  '("Theorem" "Triviality" "Proof" "QED"
    "Resume" "Finalise"
    "Theory" "Ancestors" "Libs")
  "HOL block-delimiter keywords faced with `holscript-theorem-syntax'.")

(defconst holscript-ts-mode--definition-block-keywords
  '("Definition" "Inductive" "CoInductive" "Termination"
    "Datatype" "End" "Type" "Overload")
  "HOL block-delimiter keywords faced with `holscript-definition-syntax'.")

(defconst holscript-ts-mode--single-arg-tactics
  '(;; Simplifiers / rewriters — take a theorem list.
    "simp" "gs" "gvs" "gns" "fs" "rfs"
    "rw" "REWRITE_TAC" "ASM_REWRITE_TAC"
    "ONCE_REWRITE_TAC" "ONCE_ASM_REWRITE_TAC"
    "PURE_REWRITE_TAC" "PURE_ASM_REWRITE_TAC"
    ;; First-order provers — take a theorem list.
    "metis_tac" "METIS_TAC" "MESON_TAC"
    ;; Renamers — one list or one quotation.
    "rename" "rename1"
    ;; Existential witnesses — one quotation.
    "qexists_tac" "qexists"
    ;; MP-style — take one theorem.
    "irule" "ho_match_mp_tac" "HO_MATCH_MP_TAC" "MATCH_MP_TAC")
  "Tactics that take exactly one argument.  When one of these
appears inside an `app_exp' with 3+ children, everything after
the first argument is flagged as a likely missing THEN.
Extendable via `add-to-list' for project-specific tactics.")

(defconst holscript-ts-mode--two-arg-tactics
  '(;; Simpset + theorem list.
    "simp_tac" "asm_simp_tac" "full_simp_tac"
    "SIMP_TAC" "ASM_SIMP_TAC" "FULL_SIMP_TAC"
    ;; Simpset fragment list + theorem list.
    "srw_tac" "SRW_TAC"
    ;; Position + theorem.
    "irule_at")
  "Tactics that take exactly two arguments.  Anything after the
second inside the same `app_exp' is flagged as a likely missing
THEN.")

(defun holscript-ts-mode--not-in-error-p (node)
  "Return non-nil unless NODE has an ERROR ancestor.  Used to
suppress noisy warnings inside parse-recovered regions where an
upstream typo has re-lexed nearby text.  The recovery is
transient during editing — flagging text far from the actual
error is misleading."
  (let ((n (treesit-node-parent node)))
    (while (and n (not (equal (treesit-node-type n) "ERROR")))
      (setq n (treesit-node-parent n)))
    (not n)))

(defun holscript-ts-mode--in-tactic-context-p (node)
  "Return non-nil if NODE has a `tactic' ancestor.  Used by the
missing-THEN font-lock predicates to suppress false positives
that arise mid-edit — an unfinished `Overload' or similar can
swallow following text into a non-tactic parent, and firing the
missing-THEN heuristic there produces jarring red-on-yellow
highlighting far from the cursor."
  (let ((n (treesit-node-parent node)))
    (while (and n (not (equal (treesit-node-type n) "tactic")))
      (setq n (treesit-node-parent n)))
    n))

(defconst holscript-ts-mode--tactic-combinators
  '(;; THEN family — apply tactics in sequence.
    "THEN" "THEN1" "THENL" "THEN_LT" "THENC"
    "THEN_TCL"
    ;; ORELSE family — alternative tactics.
    "ORELSE" "ORELSE_LT" "ORELSEC" "ORELSE_TCL"
    ;; Symbolic tactic combinators (Overlay.sml line 18).
    ">>" ">-" ">|" ">~" ">>~" ">>~-" ">>>" ">>-"
    "??" "?>" "\\\\"
    ;; Subgoal introducers.
    "by" "suffices_by" "via")
  "SML-side tactic combinators highlighted with `holscript-then-syntax'.
Must match the anonymous-token literals in the grammar.")

(defvar holscript-ts-mode--font-lock-feature-list
  '((comment)
    (hol-material string)
    (keyword hol-keyword name label tactic cheat definition builtin
             constant number type property syntax-error)
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
   :feature 'comment
   '((block_comment) @font-lock-comment-face)

   ;; HOL background — paint every HOL semantic region brown/bold so
   ;; theorem statements, definition bodies, quoted terms and Quote
   ;; blocks look uniform.  No :override, so later rules (keyword,
   ;; name, ...) layer on top.
   :language 'holscript
   :feature 'hol-material
   '((hol_term) @holscript-quoted-material
     (hol_thmstmt) @holscript-quoted-material
     (hol_fn_spec) @holscript-quoted-material
     (hol_inductive_body) @holscript-quoted-material
     (hol_binding) @holscript-quoted-material
     (quoted_term) @holscript-quoted-material
     (quoted_type) @holscript-quoted-material
     (backquote) @holscript-quoted-material
     (hol_quote_block) @holscript-quoted-material
     (hol_type_quotation) @holscript-quoted-material)

   :language 'holscript
   :feature 'string
   :override t
   '((string_scon) @font-lock-string-face
     (char_scon) @font-lock-constant-face
     (hol_string) @font-lock-string-face
     (hol_character) @font-lock-constant-face)

   :language 'holscript
   :feature 'keyword
   :override t
   `(;; SML keywords — DarkOliveGreen bold.
     [,@holscript-ts-mode--sml-keywords] @holscript-smlsyntax
     ;; Theorem-block delimiters — blueviolet.
     [,@holscript-ts-mode--theorem-block-keywords] @holscript-theorem-syntax
     ;; Definition-block delimiters — indianred.
     [,@holscript-ts-mode--definition-block-keywords] @holscript-definition-syntax
     ;; Fallback: when an upstream parse error re-lexes a block
     ;; keyword as a plain `vid' or a `hol_identifier' (mid-edit `>>'
     ;; or unbalanced `[' makes the recovery consume `Theorem' at
     ;; the start of a later declaration into an ongoing
     ;; expression; a broken `Definition foo: … End' can cascade
     ;; into an `hol_identifier' for `Theorem'/`Proof'/`QED'/`End'
     ;; on subsequent lines), keep the block-delimiter colour
     ;; anyway.  Real HOL code doesn't use these words as
     ;; identifiers.
     ([(vid) (hol_identifier)] @holscript-theorem-syntax
      (:match ,(rx-to-string
                `(seq bos (or ,@holscript-ts-mode--theorem-block-keywords) eos))
              @holscript-theorem-syntax))
     ([(vid) (hol_identifier)] @holscript-definition-syntax
      (:match ,(rx-to-string
                `(seq bos (or ,@holscript-ts-mode--definition-block-keywords) eos))
              @holscript-definition-syntax))
     ;; Misinterpreted identifiers matching SML reserved words or
     ;; HOL block-delimiter keywords.  Real HOL code doesn't use any
     ;; of these words as identifiers, so seeing one as a `vid' /
     ;; `tycon' / etc. means the surrounding parse has swallowed a
     ;; declaration keyword into an expression (e.g. an `Overload
     ;; foo =' missing its RHS absorbs the following `Theorem bar =
     ;; …' declaration).  Suppressed inside ERROR nodes so mid-edit
     ;; parse recovery — which re-lexes recovered text as
     ;; identifiers — doesn't splatter warnings across regions far
     ;; from the actual typo.
     ([(vid) (tycon) (strid) (sigid) (fctid)] @font-lock-warning-face
      (:match ,(rx-to-string
                `(seq bos (or ,@holscript-ts-mode--sml-keywords
                              ,@holscript-ts-mode--theorem-block-keywords
                              ,@holscript-ts-mode--definition-block-keywords)
                      eos))
              @font-lock-warning-face)
      (:pred holscript-ts-mode--not-in-error-p
             @font-lock-warning-face))
     ;; The Definition of SML excludes `*' from tycon.
     ([(tycon)] @font-lock-warning-face
      (:match ,(rx bos "*" eos) @font-lock-warning-face)
      (:pred holscript-ts-mode--not-in-error-p
             @font-lock-warning-face)))

   ;; Names of Theorems, Definitions, Datatypes, ...  — bold.
   :language 'holscript
   :feature 'name
   :override t
   '((hol_thmname) @holscript-thmname-syntax
     (hol_defname) @holscript-thmname-syntax
     (hol_typename) @holscript-thmname-syntax
     (hol_overloadname) @holscript-thmname-syntax
     (hol_theoryname) @holscript-thmname-syntax
     (hol_ancestor_name) @holscript-thmname-syntax
     (hol_lib_name) @holscript-thmname-syntax)

   ;; Definition clause labels `[~foo:]', `[/\]', ...
   :language 'holscript
   :feature 'label
   :override t
   '((hol_clause_label) @holscript-definition-label-face)

   ;; HOL-context keywords — brown bold italic.  Matched by their
   ;; enclosing HOL construct so the SML-side `if'/`then'/`else',
   ;; `case'/`of', `let'/`in', `with', etc. keep their SML face.
   ;; Runs after `keyword' so the SML face applied to shared
   ;; anonymous tokens is overridden inside HOL constructs.
   :language 'holscript
   :feature 'hol-keyword
   :override t
   '((hol_cond ["if" "then" "else"] @holscript-hol-keyword)
     (hol_case ["case" "of"] @holscript-hol-keyword)
     (hol_let ["let" "in" "and"] @holscript-hol-keyword)
     (hol_do ["do" "od"] @holscript-hol-keyword)
     (hol_record_update "with" @holscript-hol-keyword))

   ;; Tactic combinators — DarkSlateGray4 bold.  They show up in two
   ;; guises: as anonymous keyword tokens inside a `tactic' node
   ;; (`THEN' / `THENL' / `>>' etc.  between tactics), and as ordinary
   ;; `vid_exp' identifiers when they appear elsewhere in SML code
   ;; (e.g. `(op THEN)').
   :language 'holscript
   :feature 'tactic
   :override t
   `(;; Anonymous-token form: literals inside an `infix_exp' or the
     ;; tactic-specific `THEN' grammar rule.  Parent-constrained so a
     ;; HOL-level `\\' (set difference — Overlay.sml has `\\' at
     ;; both HOL infix 0 AND as a hol_binary_term operator at prec
     ;; 600) doesn't get flagged as a tactic combinator when it
     ;; appears inside a HOL term.
     ((infix_exp [,@holscript-ts-mode--tactic-combinators]
                 @holscript-then-syntax))
     ((THEN [,@holscript-ts-mode--tactic-combinators]
            @holscript-then-syntax))
     ;; Identifier form: `THEN' etc. used as an SML expression.
     ((vid_exp (longvid (vid) @holscript-then-syntax))
      (:match ,(rx-to-string
                `(seq bos (or ,@holscript-ts-mode--tactic-combinators) eos))
              @holscript-then-syntax)))

   ;; `cheat' — orange boxed.
   :language 'holscript
   :feature 'cheat
   :override t
   `((vid_exp (longvid (vid) @holscript-cheat-face)
      (:match ,(rx bos "cheat" eos) @holscript-cheat-face)))

   ;; Two tactic-composition mistakes flagged in red-on-yellow:
   ;;
   ;; 1. Successive combinators (`TAC1 THEN THEN TAC2') — the
   ;;    misplaced second combinator is absorbed by the parser into
   ;;    an `app_exp' following the correctly-parsed operator, so
   ;;    the flag is "app_exp inside infix_exp whose first
   ;;    identifier is a combinator name".
   ;;
   ;; 2. Missing combinator between two tactics — `simp [th1]
   ;;    metis_tac [th2]' parses as one 4-child `app_exp' inside a
   ;;    `tactic'.  When a known list-taking tactic (`simp', `gs',
   ;;    `metis_tac', ...) is followed by a `list_exp' and any
   ;;    further child, that further child is the "orphan next
   ;;    tactic" the user probably forgot to separate.  Each such
   ;;    extra child is flagged individually.
   :language 'holscript
   :feature 'syntax-error
   :override t
   `(((infix_exp
       _
       (app_exp
        :anchor
        (vid_exp (longvid (vid) @holscript-syntax-error-face))))
      (:match ,(rx-to-string
                `(seq bos (or ,@holscript-ts-mode--tactic-combinators) eos))
              @holscript-syntax-error-face))
     ;; Single-argument tactic (`simp TH', `irule TH', ...) with
     ;; anything beyond its one argument inside the same app_exp.
     ;; Gated on `:pred' so a mid-edit misparse that puts the
     ;; pattern under some non-tactic ancestor (e.g. a half-typed
     ;; `Overload' swallowing a nearby proof body) doesn't flag.
     ((app_exp
       :anchor
       (vid_exp (longvid (vid) @one-tac))
       :anchor
       (_)
       (_) @holscript-syntax-error-face)
      (:match ,(rx-to-string
                `(seq bos (or ,@holscript-ts-mode--single-arg-tactics) eos))
              @one-tac)
      (:pred holscript-ts-mode--in-tactic-context-p
             @holscript-syntax-error-face))
     ;; Two-argument tactic (`simp_tac SS TH', `irule_at pos TH', ...)
     ;; with anything beyond its two arguments.
     ((app_exp
       :anchor
       (vid_exp (longvid (vid) @two-tac))
       :anchor
       (_)
       :anchor
       (_)
       (_) @holscript-syntax-error-face)
      (:match ,(rx-to-string
                `(seq bos (or ,@holscript-ts-mode--two-arg-tactics) eos))
              @two-tac)
      (:pred holscript-ts-mode--in-tactic-context-p
             @holscript-syntax-error-face)))

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
       (infix_dec (vid) @font-lock-function-name-face)))

   :language 'holscript
   :feature 'builtin
   `(((vid_exp) @font-lock-builtin-face
      (:match ,(rx-to-string `(seq bos (or ,@holscript-ts-mode--sml-builtins) eos))
              @font-lock-builtin-face))
     ((vid_exp) @font-lock-preprocessor-face
      (:match ,(rx bos (or "use") eos) @font-lock-preprocessor-face)))

   :language 'holscript
   :feature 'constant
   `(((vid) @font-lock-constant-face
      (:match ,(rx bos (or "true" "false" "nil" "ref") eos)
              @font-lock-constant-face))
     (recordsel_exp ((lab) @font-lock-constant-face
                     (:match "^[0-9]+$" @font-lock-constant-face))))

   :language 'holscript
   :feature 'property
   `((tyrow (lab) @font-lock-property-name-face)
     (patrow (lab) @font-lock-property-use-face)
     (exprow (lab) @font-lock-property-use-face))

   :language 'holscript
   :feature 'type
   `((fn_ty "->" @font-lock-type-face)
     (tuple_ty "*" @font-lock-type-face)
     (paren_ty ["(" ")"] @font-lock-type-face)
     (tyvar) @font-lock-type-face
     [(strid) (sigid) (fctid)] @font-lock-type-face
     (record_ty ["{" "," "}"] @font-lock-type-face
                (tyrow [(lab) ":"] @font-lock-type-face) :?
                (ellipsis_tyrow ["..." ":"] @font-lock-type-face) :?)
     (tycon_ty (tyseq ["(" "," ")"] @font-lock-type-face) :?
               (longtycon) @font-lock-type-face))

   :language 'holscript
   :feature 'number
   '([(integer_scon) (word_scon) (real_scon)] @font-lock-number-face)))

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

(defvar holscript-ts-mode--block-kw-line-re nil
  "Cached regex matching a HOL block keyword at the start of a line.")

(defun holscript-ts-mode--line-starts-block-keyword-p (_node _parent bol)
  "Non-nil when the line at BOL begins with a HOL block keyword.
Checks the smallest node at BOL and falls back to a buffer text
match, so a `Theorem'/`Definition' recovered as an identifier
inside an ERROR still gets recognised.  Also covers `hol_quote_block'
(which is a single lexical token whose text starts with `Quote')."
  (unless holscript-ts-mode--block-kw-line-re
    (setq holscript-ts-mode--block-kw-line-re
          (rx-to-string
           `(seq (or ,@holscript-ts-mode--block-keywords) symbol-end))))
  (let ((leaf (treesit-node-at bol)))
    (or (and leaf
             (or (member (treesit-node-type leaf)
                         holscript-ts-mode--block-keywords)
                 (and (equal (treesit-node-type leaf) "hol_quote_block")
                      (= (treesit-node-start leaf) bol))))
        (save-excursion
          (goto-char bol)
          (skip-chars-forward " \t")
          (let ((case-fold-search nil))
            (looking-at-p holscript-ts-mode--block-kw-line-re))))))

(defun holscript-ts-mode--inside-error-p (_node _parent bol)
  "Non-nil when the node at BOL has an `ERROR' ancestor.
Used to suppress the ordinary parse-tree indent rules while the
buffer is mid-edit — an unfinished `Theorem foo:' can make the
recovery re-parse a large prefix as a nested `hol_application'
chain, and firing `(parent-is hol_application) parent 0' there
throws TAB to a nonsensical column."
  (let ((n (treesit-node-at bol)))
    (while (and n (not (equal (treesit-node-type n) "ERROR")))
      (setq n (treesit-node-parent n)))
    n))

(defvar holscript-ts-mode--block-opener-re nil
  "Cached regex matching a column-0 HOL block-opener keyword.")

(defun holscript-ts-mode--last-block-opener-pos (bol)
  "Position of the last column-0 HOL block-opener keyword strictly
before BOL, or nil.  A rough backward text scan — doesn't attempt
to detect closed blocks; the caller relies on this only as a
fallback when the parse tree is already broken."
  (unless holscript-ts-mode--block-opener-re
    (setq holscript-ts-mode--block-opener-re
          (rx-to-string
           `(seq line-start
                 (or ,@holscript-ts-mode--block-keywords)
                 word-end))))
  (save-excursion
    (goto-char bol)
    (forward-line 0)
    (let ((case-fold-search nil))
      (when (re-search-backward holscript-ts-mode--block-opener-re nil t)
        (point)))))

(defun holscript-ts-mode--matching-if-pos (bol)
  "Position of the `if' matching an `else' or `then' at BOL, by
backward text scan.  Each `else' seen going backward increments
the count of unmatched `else's; each `if' balances one.  Returns
nil if no matching `if' precedes BOL.  Used as a fallback when
the parse can't reach a `cond_exp' — e.g. a mid-edit
`if x then 10' with no `else' yet."
  (save-excursion
    (goto-char bol)
    (skip-chars-forward " \t")
    (let ((depth 1)
          (found nil)
          (case-fold-search nil))
      (while (and (not found)
                  (re-search-backward "\\_<\\(if\\|else\\)\\_>" nil t))
        (cond
         ((looking-at "if\\_>")
          (setq depth (1- depth))
          (when (zerop depth) (setq found (point))))
         ((looking-at "else\\_>")
          (setq depth (1+ depth)))))
      found)))

(defun holscript-ts-mode--line-starts-else-or-then-p (_node _parent bol)
  "Non-nil if the first non-whitespace text at BOL is `else' / `then'."
  (save-excursion
    (goto-char bol)
    (skip-chars-forward " \t")
    (let ((case-fold-search nil))
      (looking-at-p "\\_<\\(else\\|then\\)\\_>"))))

(defun holscript-ts-mode--line-starts-sml-topdec-kw-p (_node _parent bol)
  "Non-nil if the first non-whitespace text at BOL is an SML
top-level declaration keyword (`fun', `val', `local', ...).  Used
to keep such lines at their existing column when the surrounding
parse is broken — the swallowed decl is a real topdec that just
happens to have been absorbed upstream."
  (save-excursion
    (goto-char bol)
    (skip-chars-forward " \t")
    (let ((case-fold-search nil))
      (looking-at-p (rx-to-string
                     `(seq (or "fun" "val" "local" "type" "datatype"
                               "structure" "signature" "functor"
                               "exception" "open" "abstype" "infix"
                               "infixr" "nonfix")
                           symbol-end))))))

(defconst holscript-ts-mode--indent-rules
  `((holscript
     ;; HOL block keywords always go to column 0 of the buffer,
     ;; even when the enclosing parse is broken (mid-edit).  The
     ;; matcher checks the smallest node at bol rather than the
     ;; walked-up node so `    Theorem foo:' inside an ERROR
     ;; region still snaps to column 0.
     (holscript-ts-mode--line-starts-block-keyword-p column-0 0)
     ;; A line starting with `else' / `then' aligns with the `if'
     ;; that would match it — backward text scan counting nested
     ;; if-then-else pairs.  Fires regardless of parse state, so a
     ;; broken `if x then 10' with `else' typed on the next line
     ;; still snaps `else' under `if'.
     ((and holscript-ts-mode--line-starts-else-or-then-p
           ,(lambda (_n _p bol)
              (holscript-ts-mode--matching-if-pos bol)))
      ,(lambda (_n _p bol) (holscript-ts-mode--matching-if-pos bol))
      0)
     ;; Inside a parse-recovered region (any `ERROR' ancestor), use
     ;; the last column-0 HOL block-opener line as anchor + 2 — a
     ;; mid-edit `Definition foo:' with an incomplete body still
     ;; puts continuation text at the natural body-column.  Falls
     ;; through to the next rule (leave current indent alone) if no
     ;; block opener precedes this position.  Skipped when the line
     ;; starts with an SML top-level keyword: such lines are
     ;; genuine declarations swallowed by an upstream broken block,
     ;; and forcing them to indent would drift established code.
     ((and holscript-ts-mode--inside-error-p
           ,(lambda (n p bol)
              (not (holscript-ts-mode--line-starts-sml-topdec-kw-p n p bol)))
           ,(lambda (_n _p bol)
              (holscript-ts-mode--last-block-opener-pos bol)))
      ,(lambda (_n _p bol) (holscript-ts-mode--last-block-opener-pos bol))
      2)
     (holscript-ts-mode--inside-error-p             no-indent 0)
     ;; The body of a HOL block (statement, tactic, definition spec,
     ;; datatype binding) indents 2 from the block's start column.
     ((parent-is "\\`hol_theorem_with_proof\\'")    parent-bol 2)
     ((parent-is "\\`hol_theorem_alias\\'")         parent-bol 2)
     ((parent-is "\\`hol_definition\\'")            parent-bol 2)
     ((parent-is "\\`hol_definition_with_proof\\'") parent-bol 2)
     ((parent-is "\\`hol_inductive\\'")             parent-bol 2)
     ((parent-is "\\`hol_datatype\\'")              parent-bol 2)
     ((parent-is "\\`hol_type_alias\\'")            parent-bol 2)
     ((parent-is "\\`hol_overload\\'")              parent-bol 2)
     ((parent-is "\\`hol_theory_dec\\'")            parent-bol 2)
     ((parent-is "\\`hol_ancestors_dec\\'")         parent-bol 2)
     ((parent-is "\\`hol_libs_dec\\'")              parent-bol 2)
     ;; hol_quote_block is a single token with no inner structure.
     ((node-is   "\\`hol_quote_block\\'")           no-indent 0)
     ((parent-is "\\`hol_quote_block\\'")           no-indent 0)
     ;; Tactic chains: keep each tactic aligned with the first.
     ((parent-is "\\`tactic\\'")                    parent-bol 0)
     ;; Inside a THEN chain, align continuation lines with the
     ;; previous line's first non-blank column.  The grammar keeps
     ;; the whole chain as a single flat `THEN' node with atomic
     ;; tactics and operator tokens as siblings; each atomic on its
     ;; own line should sit at the same column as the previous.
     ((parent-is "\\`THEN\\'")                      prev-line 0)
     ;; SML application chains that span multiple lines.  Align
     ;; with the previous line's first non-blank column so `|>'
     ;; stacks under `|>'.
     ((parent-is "\\`app_exp\\'")                   prev-line 0)
     ;; SML infix chains.  Three sub-cases:
     ;;   • `by' / `suffices_by' / `via' broken onto their own line
     ;;     (subgoal-introducing infixes): indent +2 under the left
     ;;     argument, so ``goal‘\n  by tac' visually attaches the
     ;;     tactic to the quotation.
     ;;   • Any other OPERATOR on its own line (`|>' below `|>'):
     ;;     match the previous line's column so operators stack.
     ;;   • OPERAND on its own line (`simp[...]' after a `>>' on
     ;;     the previous line): align with the chain's start
     ;;     column, so operands stack at the chain regardless of
     ;;     any irregular indent between (e.g. a multi-line
     ;;     quotation continuation).
     ((and (parent-is "\\`infix_exp\\'")
           (node-is "\\`\\(by\\|suffices_by\\|via\\)\\'"))
      prev-line 2)
     ((and (parent-is "\\`infix_exp\\'")
           (node-is ,(concat
                      "\\`"
                      (regexp-opt
                       '("using"
                         "*" "/" "div" "mod" "+" "-" "^" "::" "@"
                         "=" "<>" "<" ">" "<=" ">="
                         ":=" "o" "-->" "$"
                         "++" "&&" "|->"
                         "THEN" "THEN1" "THENL" "THEN_LT" "THENC"
                         "ORELSE" "ORELSE_LT" "ORELSEC"
                         "THEN_TCL" "ORELSE_TCL"
                         "?>" "|>" "|>>" "||>" "||->"
                         ">>" ">-" ">|" "\\\\"
                         ">>>" ">>-" "??" ">~" ">>~" ">>~-"
                         "~~" "!~" "Un" "Isct" "--" "IN" "-*"
                         "##" "?"))
                      "\\'")))
      prev-line 0)
     ((parent-is "\\`infix_exp\\'")                 parent 0)
     ;; SML let / in / end.
     ((node-is   "\\`in\\'")                        parent-bol 0)
     ((node-is   "\\`end\\'")                       parent-bol 0)
     ((parent-is "\\`let_dec\\'")                   parent-bol 2)
     ;; Non-first `dec' in a `let_exp' aligns with the first `dec'
     ;; — so `let val tok1 = …\n    val tok2 = …' puts `val tok2'
     ;; under `val tok1' (indent 5 relative to `let''s line).
     ;; When the first `dec' sits on its own line, the two rules
     ;; agree: `parent-bol 2' below already puts the first `dec'
     ;; where later `dec's now anchor.
     ((and (parent-is "\\`let_exp\\'")
           (node-is "\\`\\(val\\|fun\\|type\\|datatype\\|datarepl\\|abstype\\|exception\\|open\\|local\\|infix\\|infixr\\|nonfix\\)_dec\\'")
           ,(lambda (node &rest _)
              (treesit-node-prev-sibling node t)))
      ,(lambda (_n parent &rest _)
         (treesit-node-start (treesit-node-child parent 0 t)))
      0)
     ((parent-is "\\`let_exp\\'")                   parent-bol 2)
     ;; `case'-shape (SML or HOL): a `|' aligns with the `case'
     ;; keyword itself; other children indent +2.
     ((and (node-is "\\`|\\'")
           (or (parent-is "\\`case_exp\\'")
               (parent-is "\\`hol_case\\'")))
      parent 0)
     ((parent-is "\\`case_exp\\'")                  parent 2)
     ((node-is   "\\`|\\'")                         parent-bol 2)
     ;; An SML compound expression (`case', `if', `let', `while',
     ;; `fn') opening a continuation line under `fun'/`val'/etc.
     ;; indents +2 from the enclosing declaration's line-start.
     ;; `treesit--indent-1' hands us the whole compound as `node'
     ;; when it sits at BOL, so this rule captures the "keyword at
     ;; column 0 after an unclosed opener" cases.
     ((node-is ,(concat "\\`" (regexp-opt
                               '("case_exp" "cond_exp" "iter_exp"
                                 "let_exp" "fn_exp"))
                        "\\'"))
      parent-bol 2)
     ;; SML if / then / else: branch bodies indent +2 from the
     ;; enclosing `if'.  (The grammar names this rule `cond_exp',
     ;; not `if_exp'.)
     ((node-is   "\\`then\\'")                      parent-bol 0)
     ((node-is   "\\`else\\'")                      parent-bol 0)
     ((parent-is "\\`cond_exp\\'")                  parent 2)
     ;; SML while ... do: body indents +2 from `while'.
     ((parent-is "\\`iter_exp\\'")                  parent 2)
     ;; SML record / tuple / list.  When an element sits on its own
     ;; line inside the container's brackets:
     ;;   • the first element anchors at the start of the *expression
     ;;     containing the brace* + 2 — the container's own parent
     ;;     node.  For `add_rule {…}' that's the enclosing app_exp
     ;;     `add_rule {}' at the column of `add_rule'.  For
     ;;     `f (g x y {…})' it's the inner app_exp `g x y {}',
     ;;     because the surrounding parens end the walk.
     ;;   • later elements align with the first (so `hol = …' on the
     ;;     line after `TeX = …' sits under `TeX').
     ;; Lambda anchors because Emacs 30 `treesit--simple-indent-eval'
     ;; rejects `t' as an `nth-sibling' argument.
     ((and (parent-is "\\`\\(record_exp\\|tuple_exp\\|list_exp\\)\\'")
           ,(lambda (node &rest _)
              (null (treesit-node-prev-sibling node t))))
      ,(lambda (_n parent &rest _)
         (or (and (treesit-node-parent parent)
                  (treesit-node-start (treesit-node-parent parent)))
             (treesit-node-start parent)))
      2)
     ((parent-is "\\`\\(record_exp\\|tuple_exp\\|list_exp\\)\\'")
      ,(lambda (_n parent &rest _)
         (treesit-node-start (treesit-node-child parent 0 t)))
      0)
     ;; HOL term structure — align continuation lines to the column
     ;; of the governing HOL subtree.  A one-line `A ==> B' doesn't
     ;; change; a two-line `A ==>\n  B' pulls B back to A's column
     ;; because they share the same parent `hol_binary_term'.
     ((parent-is "\\`hol_binary_term\\'")         parent 0)
     ((parent-is "\\`hol_application\\'")         parent 0)
     ;; The body of a quantifier (`!x. BODY', `?y. BODY') on a
     ;; continuation line indents 2 to the right of the binder.
     ((parent-is "\\`hol_binder\\'")              parent 2)
     ((parent-is "\\`hol_labelled_term\\'")       parent 0)
     ((parent-is "\\`hol_annotated\\'")           parent 0)
     ((parent-is "\\`hol_left_unary_term\\'")     parent 0)
     ((parent-is "\\`hol_postfix_term\\'")        parent 0)
     ((parent-is "\\`hol_universe\\'")            parent 0)
     ;; HOL if / case / let / do: bodies indent +2 from the
     ;; keyword.  For `hol_case', the `|' separators align with
     ;; `case' itself (see the SML/HOL shared `|' rule up above) —
     ;; a leading `| NONE => …' on the first row sits under `c',
     ;; while a leading `NONE => …' (no `|') sits under `s'.
     ((parent-is "\\`hol_cond\\'")                parent 2)
     ((parent-is "\\`hol_case\\'")                parent 2)
     ((parent-is "\\`hol_let\\'")                 parent 2)
     ((parent-is "\\`hol_do\\'")                  parent 2)
     ((parent-is "\\`hol_match\\'")               parent 0)
     ((parent-is "\\`hol_tuple\\'")               parent 0)
     ((parent-is "\\`hol_list\\'")                parent 0)
     ((parent-is "\\`hol_set\\'")                 parent 0)
     ((parent-is "\\`hol_record_literal\\'")      parent 0)
     ((parent-is "\\`hol_record_update\\'")       parent 0)
     ((parent-is "\\`hol_paren_op\\'")            parent 0)
     ((parent-is "\\`hol_type_quotation\\'")      parent 0)
     ;; HOL wrappers with single meaningful child — same anchor.
     ((parent-is "\\`hol_term\\'")                parent 0)
     ((parent-is "\\`hol_thmstmt\\'")             parent 0)
     ((parent-is "\\`hol_fn_spec\\'")             parent 0)
     ((parent-is "\\`hol_inductive_body\\'")      parent 0)
     ((parent-is "\\`hol_binding\\'")             parent 0)
     ;; Term-quotation wrappers.  A continuation line inside a
     ;; `‘…’' / `` ``…`` '' quotation aligns with the first
     ;; content character (right after the opening delimiter), so
     ;; `‘p ∧\n  q’' puts `q' under `p'.
     ((parent-is "\\`quoted\\'")                  parent 0)
     ((parent-is "\\`backquote\\'")               no-indent 0)
     ((parent-is "\\`quoted_term\\'")             no-indent 0)
     ;; Inside ERROR regions, leave indent alone so the user can edit
     ;; without it jumping under them.
     ((node-is   "\\`ERROR\\'")                   no-indent 0)
     ((parent-is "\\`ERROR\\'")                   no-indent 0)
     ;; Fallback for a blank line with no leaf node — a
     ;; continuation inside a top-level declaration whose parse
     ;; hasn't closed yet.  Use the last column-0 HOL block-opener
     ;; line as anchor + 2.  Restricted to `node' being nil so a
     ;; legitimate top-level `fun'/`val'/etc. isn't caught.
     ((and ,(lambda (node &rest _) (null node))
           (parent-is "\\`source_file\\'")
           ,(lambda (_n _p bol)
              (holscript-ts-mode--last-block-opener-pos bol)))
      ,(lambda (_n _p bol) (holscript-ts-mode--last-block-opener-pos bol))
      2)
     ;; Catch-all: leave the current indent unchanged.
     ((lambda (&rest _) t)                        no-indent 0))))

(defconst holscript-ts-mode--sexp-node-regexp
  (concat
   ;; Any HOL semantic node is a sexp — motion should honour the
   ;; whole HOL grammar (identifiers, atomic types, binders,
   ;; applications, block declarations, ...).
   "\\`hol_[a-z_]+\\'"
   "\\|"
   ;; SML surface node types worth stepping over as units.
   (regexp-opt
    '("tuple_exp"
      "list_exp"
      "record_exp"
      "paren_exp"
      "let_exp"
      "case_exp"
      "fn_exp"
      "if_exp"
      "app_exp"
      "vid_exp"
      "valbind"
      "fmrule"
      "tactic"
      "block_comment"
      "string_scon"
      "char_scon"
      "integer_scon"
      "word_scon"
      "real_scon"
      ;; Top-level SML declarations — the units between semicolons at
      ;; file scope.
      "val_dec" "fun_dec" "type_dec" "datatype_dec" "datarepl_dec"
      "abstype_dec" "exception_dec" "open_dec"
      "infix_dec" "infixr_dec" "nonfix_dec"
      "local_dec" "do_dec"
      "strbind" "sigbind" "fctbind"
      "structure_strdec" "signature_sigdec" "functor_fctdec"
      "local_strdec")))
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

(defun holscript-ts-mode--sexp-ancestor (node &optional min-start max-end)
  "Walk up from NODE to the nearest ancestor whose type matches
`holscript-ts-mode--sexp-node-regexp'.  If MIN-START is given, also
require that the ancestor's start is < MIN-START; if MAX-END is given,
that its end is > MAX-END.  Return nil if none."
  (let ((re holscript-ts-mode--sexp-node-regexp))
    (while (and node
                (not (and (string-match-p re
                                          (or (treesit-node-type node) ""))
                          (or (null min-start)
                              (< (treesit-node-start node) min-start))
                          (or (null max-end)
                              (> (treesit-node-end node) max-end)))))
      (setq node (treesit-node-parent node)))
    node))

(defun holscript-ts-mode--next-sexp-sibling (node backward)
  "Return the nearest sexp-typed sibling of NODE in the given direction.
BACKWARD non-nil looks at previous siblings.  Only searches at NODE's
level — does not ascend to ancestors' siblings."
  (let ((sib-fn (if backward
                    #'treesit-node-prev-sibling
                  #'treesit-node-next-sibling))
        (re holscript-ts-mode--sexp-node-regexp)
        (sib nil))
    (setq sib (funcall sib-fn node))
    (while (and sib (not (string-match-p re
                                         (or (treesit-node-type sib) ""))))
      (setq sib (funcall sib-fn sib)))
    sib))

(defun holscript-ts-mode--gap-sexp-sibling (node backward)
  "Find the nearest sexp-typed sibling of NODE or of an ancestor.
Used when NODE is punctuation with no sexp ancestor (e.g. a top-level
`;'): walks up until it finds an ancestor with a sexp-typed sibling
in the given direction."
  (let ((found nil))
    (while (and node (not found))
      (setq found (holscript-ts-mode--next-sexp-sibling node backward))
      (unless found (setq node (treesit-node-parent node))))
    found))

(defun holscript-ts-mode--backward-up-list (&optional arg)
  "Move point to the start of the innermost sexp ancestor whose start
is strictly before point.  Repeat ARG times.  Overrides `up-list' so
`C-M-u' walks structural levels directly instead of iterating
`forward-sexp' (which would descend through every intermediate sexp
sibling on the way)."
  (interactive "^p")
  (setq arg (or arg 1))
  (dotimes (_ arg)
    (let* ((pos (point))
           (target (holscript-ts-mode--sexp-ancestor
                    (treesit-node-at pos) pos nil)))
      (if target
          (goto-char (treesit-node-start target))
        (signal 'scan-error
                (list "Not enclosed by a sexp" pos pos))))))

(defun holscript-ts-mode--expand-at-boundary (node pos sign)
  "If NODE sits at a sexp boundary shared with an ancestor (SIGN > 0:
its end equals POS; SIGN < 0: its start equals POS), walk up through
sexp-typed ancestors that share the same boundary and return the
outermost.  Otherwise return NODE unchanged.  This makes motion at
the boundary of a nested chain treat the whole chain as one unit."
  (let ((boundary (if (> sign 0) #'treesit-node-end #'treesit-node-start))
        (result node))
    (when (and node (= (funcall boundary node) pos))
      (let ((up (holscript-ts-mode--sexp-ancestor
                 (treesit-node-parent node))))
        (while (and up (= (funcall boundary up) pos))
          (setq result up)
          (setq up (holscript-ts-mode--sexp-ancestor
                    (treesit-node-parent up))))))
    result))

(defun holscript-ts-mode--forward-sexp (&optional arg)
  "Move point ARG sexps forward, or backward if ARG is negative.
Bound to `forward-sexp-function' so `C-M-f' / `C-M-b' step over
tree-sitter nodes.  When motion is blocked, signal `scan-error'
with the enclosing sexp's bounds so `up-list' (`C-M-u') has a
sensible target.  Only uses primitives available in Emacs 29."
  (interactive "^p")
  (setq arg (or arg 1))
  (let ((sign (if (< arg 0) -1 1)))
    (dotimes (_ (abs arg))
      (let* ((pos (point))
             (n (or
                 ;; For backward motion, look at the node ending at
                 ;; point (i.e., containing char pos-1): the "thing
                 ;; just behind the cursor".  This lets `C-M-b' step
                 ;; over the last atom when point sits between it and
                 ;; a closing delimiter (e.g. after `tint_1' in
                 ;; `... tint_1)').  Only consult it if it actually
                 ;; ends at pos — otherwise fall through to the
                 ;; leaf-at-pos path so opening delimiters still
                 ;; behave as "outside the group".  When it does end
                 ;; at pos, expand outward to the OUTERMOST sexp that
                 ;; also ends at pos, so a chain of nested nodes
                 ;; sharing the same end (e.g. vid_exp inside
                 ;; hol_theorem_alias) is treated as one unit.
                 (and (< sign 0)
                      (> pos (point-min))
                      (let ((leaf-n (holscript-ts-mode--sexp-ancestor
                                     (treesit-node-at (1- pos)))))
                        (when (and leaf-n (= (treesit-node-end leaf-n) pos))
                          ;; Expand to the outermost sexp also ending
                          ;; at pos — but only when the character at
                          ;; point is not a closing delimiter.  At a
                          ;; closing delim (`)', `]', `”', ...), the
                          ;; user's mental model is "I'm inside the
                          ;; brackets, move over the last atom", so
                          ;; the innermost end-here match wins.
                          (unless (memq (char-after pos)
                                        '(?\) ?\] ?\} ?” ?’ ?⟧ ?⦈ ?❳ ?⟩))
                            (let ((up (holscript-ts-mode--sexp-ancestor
                                       (treesit-node-parent leaf-n))))
                              (while (and up (= (treesit-node-end up) pos))
                                (setq leaf-n up)
                                (setq up (holscript-ts-mode--sexp-ancestor
                                          (treesit-node-parent up))))))
                          leaf-n)))
                 (holscript-ts-mode--sexp-ancestor
                  (treesit-node-at pos))))
             ;; Expand to the outermost sexp sharing the same
             ;; boundary as N (forward: same end; backward at start:
             ;; same start), so nested-chain-of-single-ends is
             ;; treated as a single unit.
             (n (holscript-ts-mode--expand-at-boundary n pos sign))
             (target
              (cond
               ;; Gap: leaf is punctuation with no sexp ancestor
               ;; (e.g. a top-level `;').  Walk up until finding a
               ;; sexp-typed sibling somewhere along the ancestry.
               ((null n)
                (holscript-ts-mode--gap-sexp-sibling
                 (treesit-node-at pos) (< sign 0)))
               ((> sign 0)
                (if (> (treesit-node-end n) pos) n
                  ;; Skip past non-sexp siblings (`;', `|', etc.).
                  (holscript-ts-mode--next-sexp-sibling n nil)))
               (t
                (if (< (treesit-node-start n) pos) n
                  (holscript-ts-mode--next-sexp-sibling n t))))))
        (if (null target)
            (let ((outer (and n
                              (if (> sign 0)
                                  (holscript-ts-mode--sexp-ancestor
                                   (treesit-node-parent n) nil pos)
                                (holscript-ts-mode--sexp-ancestor
                                 (treesit-node-parent n) pos nil)))))
              (signal 'scan-error
                      (list "No more sexp to move across"
                            (if outer (treesit-node-start outer) pos)
                            (if outer (treesit-node-end outer) pos))))
          (goto-char (if (> sign 0)
                         (treesit-node-end target)
                       (treesit-node-start target))))))))

(defvar holscript-ts-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map [remap backward-up-list]
                #'holscript-ts-mode--backward-up-list)
    ;; `\`' inserts `‘’' and positions cursor between.  Pressing it
    ;; again on an existing `‘’' converts to `“”' (and vice versa).
    ;; See `holscript-dbl-backquote' in holscript-mode.el.
    (define-key map (kbd "`") #'holscript-dbl-backquote)
    map)
  "Keymap for `holscript-ts-mode'.")

;;;###autoload
(define-derived-mode holscript-ts-mode prog-mode "HOLScript[ts]"
  "Major mode for editing HOL Script.sml files with tree-sitter."
  :syntax-table holscript-ts-mode--syntax-table
  :keymap holscript-ts-mode-map

  ;; Comments — same shape as `holscript-mode-variables' uses.
  (setq-local comment-start "(* "
              comment-end " *)"
              comment-start-skip "(\\*+\\s-*"
              comment-end-skip "\\s-*\\*+)"
              comment-quote-nested nil
              parse-sexp-ignore-comments t)
  (setq-local font-lock-multiline t)
  (setq-local indent-tabs-mode nil)

  ;; Unicode substitutions (`\<=>' → `⇔' etc.) — same input method
  ;; the SMIE-based mode enables.
  (set-input-method "Hol")

  ;; Auto-pair for the HOL quotation delimiters.  Deleting the
  ;; opener of an empty `‘’' / `“”' pair also removes the closer,
  ;; matching what most editors do for `()' / `[]' / `{}'.  The
  ;; syntax table already declares these characters as balanced
  ;; open/close, so `electric-pair-mode' recognises them without
  ;; further configuration.
  (electric-pair-local-mode 1)

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
    ;; keep it set for feature-parity with modes that rely on things.
    (setq-local treesit-thing-settings
                holscript-ts-mode--thing-settings)
    (when (boundp 'treesit-sentence-type-regexp)
      (setq-local treesit-sentence-type-regexp
                  holscript-ts-mode--sentence-node-regexp))

    ;; Indent
    (setq-local treesit-simple-indent-rules
                holscript-ts-mode--indent-rules)

    (treesit-major-mode-setup)

    ;; `C-M-f' / `C-M-b'.  Wire a local mover that walks the parse
    ;; tree using only primitives available in Emacs 29; the built-in
    ;; `treesit-forward-sexp' relies on `treesit-thing-defined-p'
    ;; (Emacs 30 only) to resolve the `sexp' thing, and silently
    ;; falls back to word-level motion on 29 when it errors.
    (setq-local forward-sexp-function #'holscript-ts-mode--forward-sexp)))

(provide 'holscript-ts-mode)
