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
         (modedir (concat holdir "tools/editor-modes/emacs/tree-sitter/")))
    (add-to-list 'load-path modedir)
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

(provide 'holscript-ts-tests)
;;; holscript-ts-tests.el ends here
