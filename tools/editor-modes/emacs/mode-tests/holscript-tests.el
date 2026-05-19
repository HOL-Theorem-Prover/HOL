;;; run with something like
;;;  HOLDIR=<dir> emacs -batch -l ert -l holscript-tests.el -f ert-run-tests-batch-and-exit

(load (concat (file-name-as-directory (getenv "HOLDIR")) "tools/editor-modes/emacs/hol-mode"))

(defun holscript-fixture-in (file sword-arg body)
  (with-temp-buffer
    (insert-file-contents-literally
     (concat hol-dir "tools/editor-modes/emacs/mode-tests/" file))
    (decode-coding-region (point-min) (point-max) 'utf-8-unix)
    (holscript-mode)
    (set-buffer-modified-p nil)
    (superword-mode sword-arg)
    (funcall body)))

(defun holscript-fixture-both (file body)
  (holscript-fixture-in file 0 body)
  (holscript-fixture-in file 1 body))


(defun holscript-unchanged-at1 (p)
  ;; (message "Testing unchanged at %d" (line-number-at-pos))
  (indent-for-tab-command)
  (not (buffer-modified-p)))

(defun holscript-unchanged-at (posns)
  (save-excursion
    (let ((ps posns))
      (while (and (not (null ps))
                  (goto-char (car ps))
                  (setq ps (cdr ps))
                  (holscript-unchanged-at1)))
      (null ps))))

(defun holscript-eachline-unchanged ()
  (save-excursion
    (goto-char (point-min))
    (while (and (should (holscript-unchanged-at1 (point)))
                (equal 0 (forward-line))))))

(ert-deftest holscript-indent1 ()
  "Tests every line in sampleScript is already indented correctly"
  (holscript-fixture-both "indentScript.sml" 'holscript-eachline-unchanged))

(defun holscript-indent2-test ()
  (goto-char 86)
  (insert " \t  ")
  (indent-for-tab-command)
  (should (= (point) 86))
  (should (looking-at "^Theorem.bar:")))

(ert-deftest holscript-indent2 ()
  "Tests Theorem: syntax after Theorem="
  (holscript-fixture-both "indentScript.sml" 'holscript-indent2-test))

(defun holscript-indent3-test ()
  (goto-char 111)
  (insert "\n")
  (indent-for-tab-command)
  (should (= (point) 114))
  (beginning-of-line)
  (should (= (point) 112))
  (should (looking-at "  simp\\[]")))
(ert-deftest holscript-indent3 ()
  "Tactic indents 2 when moved under proof keyword (_)"
  (holscript-fixture-both "indentScript.sml" 'holscript-indent3-test))


(defun holscript-indent4-test ()
  (goto-char 214)
  (insert "\n>-")
  (indent-for-tab-command)
  (beginning-of-line)
  (should (= (point) 215))
  (should (looking-at "  >-")))
(ert-deftest holscript-indent4 ()
  "Tactic indents to parent level 2, after >- (w)"
  (holscript-fixture-both "sampleScript.sml" 'holscript-indent4-test))

(defun move-check (posns mover)
  (goto-char (car posns))
  (let ((ps (cdr posns)))
    (catch 'exit
      (while (not (null ps))
        (funcall mover)
        (if (not (= (point) (car ps)))
            (progn
              (message "At %d, wanted to be at %d" (point) (car ps))
              (throw 'exit nil)))
        (setq ps (cdr ps)))
      t)))


(defun holscript-sexp-movement-test ()
  (save-excursion
    (and
     (should (move-check '(1 12 41 42 64 84 121 139
                             176 218 382 499)
                         'forward-sexp))
     (should (move-check '(2205 2486) 'forward-sexp))
     (should (move-check '(3872 3905) 'forward-sexp))
     (should (move-check '(3507 3310) 'backward-up-list))
     (should (move-check '(3907 3872 3310 2801) 'backward-sexp))
     (should (move-check '(4435 4452 4505 4552) 'forward-sexp))
     (should (move-check '(4455 4505) 'forward-sexp))
     (should (move-check '(4508 4455 4435) 'backward-sexp))
     (should (move-check '(3943 3959 3999 4046) 'forward-sexp))
     (should (move-check '(4599 4558) 'backward-sexp))
     (should (move-check '(5955 5315 4673 4602) 'backward-sexp)))))

(ert-deftest holscript-sexp-movement ()
  "sexp-moves are made correctly"
  (holscript-fixture-both "sampleScript.sml" 'holscript-sexp-movement-test))

(defconst point4359-expected
  " (*#loc 261 10 *)\ninv (2r pow (e + 1)) < inv (2r pow e)")
(defun holscript-tap-test ()
  (should (save-excursion
            (and
             (progn (goto-char 4359)
                    (equal (hol-term-at-point) point4359-expected))))))

(ert-deftest holscript-term-at-point ()
  "hol-term-at-point correct"
  (holscript-fixture-both "sampleScript.sml" 'holscript-tap-test))

(defun hol-module-qualification-fullmatch-p (s)
  (let ((m (string-match hol-module-qualification-regexp s)))
    (and m (= 0 m) (= (match-end 0) (length s)))))

(ert-deftest hol-module-qualification-regexp-attrs ()
  "Attribute block regexp matches names/values containing _ and other
identifier-class characters."
  (should (hol-module-qualification-fullmatch-p "[ignore_grammar]"))
  (should (hol-module-qualification-fullmatch-p " [bare]"))
  (should (hol-module-qualification-fullmatch-p "[induction=foo_bar]"))
  (should (hol-module-qualification-fullmatch-p "[a, b_c, d=e]"))
  (should (hol-module-qualification-fullmatch-p "[\n  ignore_grammar\n]"))
  (should-not (hol-module-qualification-fullmatch-p "ignore_grammar"))
  (should-not (hol-module-qualification-fullmatch-p "[unterminated")))

(defun holscript-record-loads (input thunk)
  "Insert INPUT into a holscript-mode buffer, advise hol-load-string to
record its argument, run THUNK from point-min, and return the recorded
arguments in call order."
  (let ((loads nil))
    (cl-letf (((symbol-function 'hol-load-string)
               (lambda (s) (push s loads))))
      (with-temp-buffer
        (let ((holscript-mode-hook nil)) (holscript-mode))
        (insert input)
        (goto-char (point-min))
        (funcall thunk))
      (nreverse loads))))

(ert-deftest hol-load-modules-in-region-skips-underscored-attr ()
  "Per-ancestor [foo_bar] attributes must not leak as module names."
  (should
   (equal
    (holscript-record-loads
     "foo[ignore_grammar] bar"
     (lambda ()
       (hol-load-modules-in-region t (point-min) (point-max))))
    '("fooTheory" "barTheory"))))

(ert-deftest hol-ancestors-attribute-block-skipped ()
  "Attribute on the Ancestors keyword itself is skipped (mirrors the
relevant slice of send-string-to-hol's behaviour after matching
Ancestors); the bracketed attribute name must not be loaded as a
module."
  (should
   (equal
    (holscript-record-loads
     "Ancestors[ignore_grammar]\n  wordConvs parmove\n"
     (lambda ()
       (re-search-forward "^Ancestors\\_>")
       (when (looking-at hol-module-qualification-regexp)
         (goto-char (match-end 0)))
       (hol-load-modules-in-region t (point) (point-max))))
    '("wordConvsTheory" "parmoveTheory"))))
