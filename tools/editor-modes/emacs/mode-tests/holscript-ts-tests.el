;;; holscript-ts-tests.el --- ERT tests for holscript-ts-mode -*- lexical-binding: t -*-

;;; Commentary:
;;
;; Run with:
;;   HOLDIR=<dir> emacs -batch -l ert \
;;     -l mode-tests/holscript-ts-tests.el -f ert-run-tests-batch-and-exit
;;
;; Requires Emacs 29+ (treesit) and the `holscript' tree-sitter parser
;; library (libtree-sitter-holscript.so) on `treesit-extra-load-path' or
;; in ~/.emacs.d/tree-sitter/.  Each test skips itself when those
;; preconditions aren't met, so the file can be loaded under Emacs 28
;; without erroring.

;;; Code:

(require 'ert)
(when (and (require 'treesit nil t)
           (treesit-available-p))
  (let* ((holdir (file-name-as-directory (getenv "HOLDIR")))
         (modedir (concat holdir "tools/editor-modes/emacs/tree-sitter/"))
         (parserdir (concat modedir "tree-sitter-holscript/")))
    (add-to-list 'load-path modedir)
    ;; Look for the parser library alongside the mode source, so tests
    ;; use the current tree matching the current grammar rather than
    ;; a possibly-stale copy in `~/.emacs.d/tree-sitter/'.
    (add-to-list 'treesit-extra-load-path parserdir)
    (require 'holscript-ts-mode nil t)))

(defun holscript-ts-tests--preconds ()
  "Return non-nil iff tree-sitter and the holscript parser are ready."
  (and (featurep 'treesit)
       (treesit-available-p)
       (treesit-language-available-p 'holscript)
       (fboundp 'holscript-ts-mode)))

(defun holscript-ts-tests--fixture (file body)
  "Insert FILE (relative to HOLDIR/tools/editor-modes/emacs/mode-tests/)
into a fresh holscript-ts-mode buffer and call BODY."
  (with-temp-buffer
    (insert-file-contents-literally
     (concat (file-name-as-directory (getenv "HOLDIR"))
             "tools/editor-modes/emacs/mode-tests/" file))
    (decode-coding-region (point-min) (point-max) 'utf-8-unix)
    (holscript-ts-mode)
    (set-buffer-modified-p nil)
    (funcall body)))

;; --- Defun navigation --------------------------------------------------------

(defun holscript-ts-tests--collect-defuns ()
  "Walk every defun in the current buffer; return a list of
\(NODE-TYPE . NAME) pairs."
  (let (out (last -1))
    (goto-char (point-max))
    (while (and (condition-case nil (treesit-beginning-of-defun)
                  (error nil))
                (/= (point) last))
      (setq last (point))
      (let ((node (treesit-defun-at-point)))
        (when node
          (push (cons (treesit-node-type node) (treesit-defun-name node))
                out)))
      (unless (bobp) (forward-char -1)))
    out))

(ert-deftest holscript-ts-defun-names ()
  "treesit-defun-name returns the user-visible name for each kind of
top-level HOL block / SML declaration we care about."
  (skip-unless (holscript-ts-tests--preconds))
  (holscript-ts-tests--fixture
   "sampleScript.sml"
   (lambda ()
     (let* ((defuns (holscript-ts-tests--collect-defuns))
            (kinds (mapcar #'car defuns))
            (names (mapcar #'cdr defuns)))
       (should (member "hol_theorem_with_proof" kinds))
       (should (member "hol_definition" kinds))
       (should (member "hol_datatype" kinds))
       (should (member "val_dec" kinds))
       (should (member "foo0" names))
       (should (member "EXISTS_i2mw" names))
       (should (member "foo" names))))))

;; --- Imenu ------------------------------------------------------------------

(ert-deftest holscript-ts-imenu-shape ()
  "Imenu produces a Theorem / Definition / Datatype categorised index."
  (skip-unless (holscript-ts-tests--preconds))
  (holscript-ts-tests--fixture
   "sampleScript.sml"
   (lambda ()
     (let ((index (funcall imenu-create-index-function)))
       (should (assoc "Theorem" index))
       (should (assoc "Definition" index))
       (should (assoc "Datatype" index))
       (let ((thms (mapcar #'car (cdr (assoc "Theorem" index)))))
         (should (member "EXISTS_i2mw" thms))
         (should (member "foo0" thms)))))))

;; --- Sexp motion ------------------------------------------------------------

(ert-deftest holscript-ts-sexp-motion-jumps-blocks ()
  "forward-sexp from buffer start moves over the first top-level
construct (an open declaration, val declaration, or Theorem)."
  (skip-unless (holscript-ts-tests--preconds))
  (holscript-ts-tests--fixture
   "sampleScript.sml"
   (lambda ()
     (goto-char (point-min))
     (let ((before (point)))
       (forward-sexp)
       (should (> (point) before))))))

;; --- Indent -----------------------------------------------------------------

(defun holscript-ts-tests--indent-line ()
  "Return the column that `treesit-indent' would set this line to,
without leaving the buffer's whitespace re-arranged."
  (let* ((bol (line-beginning-position))
         (eol (line-end-position))
         (original-line (buffer-substring bol eol)))
    (treesit-indent)
    (prog1 (save-excursion (back-to-indentation) (current-column))
      (delete-region (line-beginning-position) (line-end-position))
      (insert original-line))))

(ert-deftest holscript-ts-indent-block-keywords-at-col-0 ()
  "Theorem / Proof / QED / Definition / End / Datatype: lines indent
to column 0."
  (skip-unless (holscript-ts-tests--preconds))
  (holscript-ts-tests--fixture
   "indentScript.sml"
   (lambda ()
     (goto-char (point-min))
     (let ((checked 0))
       (while (re-search-forward
               "^\\(Theorem\\|Proof\\|QED\\|Definition\\|End\\|Datatype:\\)\\b"
               nil t)
         (beginning-of-line)
         (should (= 0 (holscript-ts-tests--indent-line)))
         (setq checked (1+ checked))
         (forward-line 1))
       (should (> checked 5))))))

(ert-deftest holscript-ts-indent-body-by-two ()
  "Direct children of a hol_theorem_with_proof / hol_definition body
indent to column 2 (when the parser doesn't classify them under
ERROR)."
  (skip-unless (holscript-ts-tests--preconds))
  (holscript-ts-tests--fixture
   "indentScript.sml"
   (lambda ()
     ;; Pick a few lines we *know* are clean theorem bodies.
     (dolist (target '("  all_tac"
                       "  Cases \\\\ SIMP_TAC std_ss [Excl \"lift_disj_eq\"]"))
       (goto-char (point-min))
       (should (search-forward target nil t))
       (beginning-of-line)
       (should (= 2 (holscript-ts-tests--indent-line)))))))

;; --- Inline-content indent helper -------------------------------------------

(defmacro holscript-ts-tests--with-string (content &rest body)
  "Set up a holscript-ts-mode buffer with CONTENT and run BODY."
  (declare (indent 1))
  `(with-temp-buffer
     (insert ,content)
     (holscript-ts-mode)
     (set-buffer-modified-p nil)
     ,@body))

(defun holscript-ts-tests--indent-after-strip (regex)
  "Find the first line matching REGEX, delete its leading whitespace,
call `indent-for-tab-command', return the resulting column."
  (goto-char (point-min))
  (should (re-search-forward regex nil t))
  (beginning-of-line)
  (delete-region (point) (progn (skip-chars-forward " \t") (point)))
  (indent-for-tab-command)
  (current-indentation))

;; --- Indent: SML compound-expression at BOL ---------------------------------

(ert-deftest holscript-ts-indent-case-at-bol ()
  "`case x of' as a continuation line under `fun f x =' snaps to col 2."
  (skip-unless (holscript-ts-tests--preconds))
  (holscript-ts-tests--with-string
      "fun f x =\ncase x of\n    [] => 3\n  | h::t => h + f t\n"
    (should (= 2 (holscript-ts-tests--indent-after-strip "^case ")))))

(ert-deftest holscript-ts-indent-if-at-bol ()
  "`if …' as a continuation line under `fun f x =' snaps to col 2."
  (skip-unless (holscript-ts-tests--preconds))
  (holscript-ts-tests--with-string
      "fun f x =\nif x then 1 else 2\n"
    (should (= 2 (holscript-ts-tests--indent-after-strip "^if ")))))

(ert-deftest holscript-ts-indent-let-at-bol ()
  "`let …' as a continuation line under `fun f x =' snaps to col 2."
  (skip-unless (holscript-ts-tests--preconds))
  (holscript-ts-tests--with-string
      "fun f x =\nlet val a = 1 in a end\n"
    (should (= 2 (holscript-ts-tests--indent-after-strip "^let ")))))

(ert-deftest holscript-ts-indent-while-at-bol ()
  "`while …' as a continuation line under `fun f () =' snaps to col 2."
  (skip-unless (holscript-ts-tests--preconds))
  (holscript-ts-tests--with-string
      "fun f () =\nwhile true do print \"x\"\n"
    (should (= 2 (holscript-ts-tests--indent-after-strip "^while ")))))

(ert-deftest holscript-ts-indent-fn-at-bol ()
  "`fn …' as a continuation line under `fun f x =' snaps to col 2."
  (skip-unless (holscript-ts-tests--preconds))
  (holscript-ts-tests--with-string
      "fun f x =\nfn y => y\n"
    (should (= 2 (holscript-ts-tests--indent-after-strip "^fn ")))))

;; --- Indent: case-shape internals -------------------------------------------

(ert-deftest holscript-ts-indent-case-first-mrule ()
  "`[] => 3' inside a case_exp at col 2 indents to col 4."
  (skip-unless (holscript-ts-tests--preconds))
  (holscript-ts-tests--with-string
      "fun f x =\n  case x of\n[] => 3\n  | h::t => h + f t\n"
    (should (= 4 (holscript-ts-tests--indent-after-strip "^\\[\\]")))))

(ert-deftest holscript-ts-indent-case-pipe-aligns-with-case ()
  "`| h::t => …' inside a case_exp aligns with the `case' keyword."
  (skip-unless (holscript-ts-tests--preconds))
  (holscript-ts-tests--with-string
      "fun f x =\n  case x of\n    [] => 3\n| h::t => h + f t\n"
    (should (= 2 (holscript-ts-tests--indent-after-strip "^| ")))))

;; --- Indent: container elements ---------------------------------------------

(ert-deftest holscript-ts-indent-record-first-element ()
  "First element on its own line inside a record anchors at the
enclosing expression + 2 (`f x y {\\n  fld = …' puts `fld' at col 4)."
  (skip-unless (holscript-ts-tests--preconds))
  (holscript-ts-tests--with-string
      "val z =\n  f x y {\nfld = foo, fld = bar,\n  fld = qux\n  }\n"
    (should (= 4 (holscript-ts-tests--indent-after-strip "^fld = foo")))))

(ert-deftest holscript-ts-indent-record-first-element-nested-parens ()
  "First element inside a nested-paren record respects parens:
`f (g x y {\\n  fld = …' anchors at `g' + 2, not `f' + 2."
  (skip-unless (holscript-ts-tests--preconds))
  (holscript-ts-tests--with-string
      "val z =\n  f (g x y {\nfld = foo\n     })\n"
    (should (= 7 (holscript-ts-tests--indent-after-strip "^fld = foo")))))

(ert-deftest holscript-ts-indent-record-later-elements-align-with-first ()
  "A later record field on its own line aligns with the first named
child (the first `exprow')."
  (skip-unless (holscript-ts-tests--preconds))
  (holscript-ts-tests--with-string
      "val r = {TeX = 1,\nhol = 2}\n"
    (should (= 9 (holscript-ts-tests--indent-after-strip "^hol = 2")))))

;; --- Indent: let-decl alignment ---------------------------------------------

(ert-deftest holscript-ts-indent-let-inline-first-val-align ()
  "`let val tok1 = …\\n    val tok2 = …' aligns the second `val'
with the first (col 6 relative to `let' at col 2)."
  (skip-unless (holscript-ts-tests--preconds))
  (holscript-ts-tests--with-string
      "fun f _ =\n  let val tok1 = \"a\"\nval tok2 = \"b\"\n  in tok1 end\n"
    (should (= 6 (holscript-ts-tests--indent-after-strip "^val tok2")))))

(ert-deftest holscript-ts-indent-let-on-own-line-vals-at-col-4 ()
  "`let\\n  val tok1 = …\\n  val tok2 = …' with `let' at col 2 puts
the second `val' at col 4."
  (skip-unless (holscript-ts-tests--preconds))
  (holscript-ts-tests--with-string
      "fun f _ =\n  let\n    val tok1 = \"a\"\nval tok2 = \"b\"\n  in tok1 end\n"
    (should (= 4 (holscript-ts-tests--indent-after-strip "^val tok2")))))

;; --- Indent: broken-block cascade recovery ----------------------------------

(ert-deftest holscript-ts-indent-broken-def-blank-line-to-col-2 ()
  "A blank continuation line inside a broken `Definition' indents
to column 2 (last column-0 block-opener + 2)."
  (skip-unless (holscript-ts-tests--preconds))
  (holscript-ts-tests--with-string
      "Theory foo
Ancestors hol
Libs boolLib

Definition foo:
f x y = if x < y then 10

"
    (goto-char (point-max))
    (indent-for-tab-command)
    (should (= 2 (current-indentation)))))

(ert-deftest holscript-ts-indent-else-aligns-with-if ()
  "`else' typed at BOL inside a broken `if x then N' aligns with `if'."
  (skip-unless (holscript-ts-tests--preconds))
  (holscript-ts-tests--with-string
      "Theory foo
Ancestors hol
Libs boolLib

Definition foo:
f x y = if x < y then 10
else
"
    (should (= 8 (holscript-ts-tests--indent-after-strip "^else\\b")))))

(ert-deftest holscript-ts-indent-following-theorem-stays-at-col-0 ()
  "A well-formed `Theorem …' after a broken `Definition' stays at
column 0 — the block-keyword-line predicate falls through to a text
match when the parse re-lexes `Theorem' as a `hol_identifier'."
  (skip-unless (holscript-ts-tests--preconds))
  (holscript-ts-tests--with-string
      "Definition foo:
f x y = if
Theorem existing = TRUTH
"
    (should (= 0 (holscript-ts-tests--indent-after-strip "^Theorem existing")))))

;; --- Indent: quotation continuation -----------------------------------------

(ert-deftest holscript-ts-indent-quotation-continuation-aligns-with-content ()
  "Content on a continuation line inside `‘…’' aligns with the first
content character (right after the opening delimiter)."
  (skip-unless (holscript-ts-tests--preconds))
  (holscript-ts-tests--with-string
      "Theorem foo:
  p ∧ q
Proof
  ‘p ∧
q’ by tac
QED
"
    (should (= 3 (holscript-ts-tests--indent-after-strip "^q’")))))

;; --- Sexp motion in HOL material --------------------------------------------

(ert-deftest holscript-ts-sexp-inside-quotation-uses-syntax-motion ()
  "Inside a `quoted' region (opaque to tree-sitter), back-sexp uses
standard syntax-based motion — from a space inside `(q + z * 2)'
it moves left one word/char, staying inside the parens."
  (skip-unless (holscript-ts-tests--preconds))
  (holscript-ts-tests--with-string
      "Theorem foo:\n  T\nProof\n  ‘f (q + z)’ by tac\nQED\n"
    ;; Point on the space between `q' and `+' inside the parens.
    (goto-char (point-min))
    (should (search-forward "q + " nil t))
    ;; Position after the space; go back one char to land on the space
    ;; itself so back-sexp moves across `q'.
    (backward-char 2)
    (let ((start (point)))
      (backward-sexp)
      (should (< (point) start))
      ;; Should stay to the right of the opening `(' — i.e. inside parens.
      (should (progn
                (goto-char start)
                (search-backward "(" nil t)
                (< (point) start))))))

(ert-deftest holscript-ts-sexp-backward-across-infix-rhs ()
  "back-sexp from the RHS of an infix chain steps to the LHS."
  (skip-unless (holscript-ts-tests--preconds))
  (holscript-ts-tests--with-string
      "Theorem foo:\n  T\nProof\n  simp[]\n  >> gvs[]\nQED\n"
    (goto-char (point-min))
    (should (search-forward "gvs[]" nil t))
    (search-backward "gvs")
    (let ((start (point)))
      (backward-sexp)
      (should (< (point) start))
      ;; The previous sexp is `simp[]', so we should land at or before it.
      (goto-char (point-min))
      (should (search-forward "simp[]" nil t))
      (search-backward "simp"))))

(ert-deftest holscript-ts-sexp-forward-over-quotation ()
  "forward-sexp at the opening `‘' jumps just past the closing `’',
not out to the enclosing tactic's end."
  (skip-unless (holscript-ts-tests--preconds))
  (holscript-ts-tests--with-string
      "Theorem foo:\n  T\nProof\n  ‘p ∧ q’ by tac\nQED\n"
    (goto-char (point-min))
    (should (search-forward "‘" nil t))
    (backward-char 1)
    (forward-sexp)
    ;; Should land immediately after the closing `’'.
    (should (equal (char-before) ?’))))

;; --- Font-lock: block keywords in a cascade ---------------------------------

(ert-deftest holscript-ts-font-lock-block-keyword-as-hol-identifier ()
  "When a broken `Definition' cascades into an ERROR that re-lexes a
downstream `Theorem'/`Proof'/`QED'/`End' as `hol_identifier's, those
keywords still carry the block-syntax face."
  (skip-unless (holscript-ts-tests--preconds))
  (holscript-ts-tests--with-string
      "Theory foo
Ancestors hol
Libs boolLib

Definition foo:
  f x y = if
End

Theorem bar:
  p
Proof
  strip_tac
QED
"
    (font-lock-ensure)
    (dolist (kw '(("End"     . holscript-definition-syntax)
                  ("Theorem" . holscript-theorem-syntax)
                  ("Proof"   . holscript-theorem-syntax)
                  ("QED"     . holscript-theorem-syntax)))
      (goto-char (point-min))
      (should (re-search-forward (concat "^" (regexp-quote (car kw)) "\\b") nil t))
      (let ((face (get-text-property (match-beginning 0) 'face)))
        (should (eq face (cdr kw)))))))

(ert-deftest holscript-ts-font-lock-misplaced-sml-keyword-flagged ()
  "A `val'-as-`vid' inside an unfinished `Overload foo =' RHS is
flagged with `font-lock-warning-face'."
  (skip-unless (holscript-ts-tests--preconds))
  (holscript-ts-tests--with-string
      "Theory foo\nAncestors hol\n\nOverload AndT =\n\nval x = 3\n\nTheorem foo = TRUTH\n"
    (font-lock-ensure)
    (goto-char (point-min))
    (should (re-search-forward "^val " nil t))
    (goto-char (match-beginning 0))
    (should (eq 'font-lock-warning-face (get-text-property (point) 'face)))))

(ert-deftest holscript-ts-font-lock-misplaced-hol-block-keyword-flagged ()
  "A `Theorem'-as-`vid' absorbed into an unfinished `Overload foo ='
RHS is flagged with `font-lock-warning-face'."
  (skip-unless (holscript-ts-tests--preconds))
  (holscript-ts-tests--with-string
      "Theory foo\nAncestors hol\n\nOverload AndT =\n\nTheorem foo = TRUTH\n"
    (font-lock-ensure)
    (goto-char (point-min))
    (should (re-search-forward "^Theorem foo" nil t))
    (goto-char (match-beginning 0))
    (should (eq 'font-lock-warning-face (get-text-property (point) 'face)))))

(provide 'holscript-ts-tests)
;;; holscript-ts-tests.el ends here
