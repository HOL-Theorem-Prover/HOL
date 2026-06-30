;;; holscript-bench.el --- Microbench for holscript-mode -*- lexical-binding: t -*-

;; Run with:
;;   HOLDIR=<dir> emacs -batch -l holscript-bench.el -f holscript-bench-run
;;
;; The bench loads holscript-mode against a synthetic large buffer in
;; two shapes:
;;
;;   "balanced"   N completed `Theorem foo : ... QED` blocks, so any
;;                position in the buffer has a `Theorem`/`QED`
;;                delimiter within a few lines either side.
;;
;;   "no-close"  One `Theorem foo:` header at the top followed by
;;                many tactic-like lines without any closing `QED`,
;;                `End`, `Proof`, `Termination`, or quoted-material
;;                delimiter.  Backward search from late positions has
;;                to scan back to the lone header; forward search has
;;                to scan all the way to point-max.  Models the
;;                "user has typed an unterminated block" scenario the
;;                user reported.
;;
;; Each shape exercises the hot paths the perf fix targets:
;;   * `hol-fl-extend-region'        (font-lock-extend-region hook)
;;   * `holscript-in-quotedmaterialp'
;;   * `holscript-smie-forward-token'   (which calls both of those)

(require 'cl-lib)

;; Declared special so `let' below binds them dynamically (font-lock
;; calls `hol-fl-extend-region' with these dynamically bound).
(defvar font-lock-beg)
(defvar font-lock-end)

(defun holscript-bench--load-mode ()
  (let* ((holdir (file-name-as-directory (getenv "HOLDIR")))
         (modedir (concat holdir "tools/editor-modes/emacs/")))
    (add-to-list 'load-path modedir)
    (load (concat modedir "hol-mode"))))

(defun holscript-bench--make-balanced (n-blocks)
  (insert "open HolKernel Parse boolLib bossLib;\n")
  (insert "val _ = new_theory \"bench\";\n\n")
  (dotimes (i n-blocks)
    (insert (format
             (concat
              "Theorem foo_%d:\n"
              "  !x y z. x + y + z = z + y + x\n"
              "Proof\n"
              "  rpt strip_tac \\\\\n"
              "  simp[] \\\\\n"
              "  metis_tac[]\n"
              "QED\n\n")
             i)))
  (insert "val _ = export_theory();\n"))

(defun holscript-bench--make-no-close (n-lines)
  (insert "open HolKernel Parse boolLib bossLib;\n")
  (insert "val _ = new_theory \"bench\";\n\n")
  (insert "Theorem foo:\n")
  (insert "  !x y. P x y\n")
  (insert "Proof\n")
  ;; Many tactic-like lines without any closing delimiter.
  (dotimes (i n-lines)
    (insert (format "  rpt strip_tac >> simp[] >> rw[] (* %d *)\n" i))))

(defun holscript-bench--time (label body)
  (let ((gc-cons-threshold (* 64 1024 1024))
        (gc-cons-percentage 0.5))
    (garbage-collect)
    (let* ((t0 (current-time))
           (_ (funcall body))
           (elapsed (float-time (time-subtract (current-time) t0))))
      (message "  %-42s %8.3f s" label elapsed)
      elapsed)))

(defun holscript-bench--positions (reps margin)
  "Return a list of REPS positions spread across the active buffer,
staying at least MARGIN chars from each edge."
  (let* ((lo (1+ margin))
         (hi (max (1+ lo) (- (point-max) margin)))
         (span (- hi lo))
         (out  nil))
    (dotimes (i reps)
      (push (+ lo (mod (* (1+ i) 7919) span)) out))
    out))

(defun holscript-bench--call-extend-region (positions)
  (dolist (p positions)
    (let ((font-lock-beg p)
          (font-lock-end (min (point-max) (+ p 80))))
      (hol-fl-extend-region))))

(defun holscript-bench--call-quotedmaterialp (positions)
  (dolist (p positions)
    (holscript-in-quotedmaterialp p)))

(defun holscript-bench--smie-walk ()
  "Step every HOL-SMIE token in the buffer forward once."
  (save-excursion
    (goto-char (point-min))
    (let ((p -1))
      (while (and (not (eobp)) (/= p (point)))
        (setq p (point))
        (let ((tok (holscript-smie-forward-token)))
          (when (and (not (eobp)) (stringp tok) (string-empty-p tok))
            (forward-char 1)))))))

(defun holscript-bench--run-case (label maker)
  (with-temp-buffer
    (let ((holscript-mode-hook nil))
      (funcall maker)
      (holscript-mode))
    (message " case: %-10s  buffer-size: %d chars  lines: %d"
             label (buffer-size)
             (count-lines (point-min) (point-max)))
    (let ((positions (holscript-bench--positions 500 100)))
      (holscript-bench--time
       (format "extend-region x500 (%s)" label)
       (lambda () (holscript-bench--call-extend-region positions)))
      (holscript-bench--time
       (format "in-quotedmaterialp x500 (%s)" label)
       (lambda () (holscript-bench--call-quotedmaterialp positions))))
    (holscript-bench--time
     (format "smie-walk forward (%s)" label)
     #'holscript-bench--smie-walk)))

(defun holscript-bench-run ()
  (holscript-bench--load-mode)
  (dolist (n-blocks '(200 800 2000))
    (message "\n=== balanced %d blocks ===========================" n-blocks)
    (holscript-bench--run-case
     "balanced"
     (lambda () (holscript-bench--make-balanced n-blocks))))
  (dolist (n-lines '(2000 8000 20000))
    (message "\n=== no-close %d lines ============================" n-lines)
    (holscript-bench--run-case
     "no-close"
     (lambda () (holscript-bench--make-no-close n-lines)))))

(provide 'holscript-bench)
;;; holscript-bench.el ends here
