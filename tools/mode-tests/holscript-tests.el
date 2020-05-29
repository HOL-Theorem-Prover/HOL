;;; run with something like
;;;  HOLDIR=<dir> emacs -batch -l ert -l holscript-tests.el -f ert-run-tests-batch-and-exit

(load (concat (file-name-as-directory (getenv "HOLDIR")) "tools/hol-mode"))

(defun holscript-fixture-in (file uscore_str body)
  (with-temp-buffer
    (insert-file-contents-literally (concat holdir "tools/mode-tests/" file))
    (decode-coding-region (point-min) (point-max) 'utf-8-unix)
    (holscript-mode)
    (set-buffer-modified-p nil)
    (modify-syntax-entry ?_ uscore_str holscript-mode-syntax-table)
    (funcall body)))


(defun holscript-unchanged-at1 ()
  ; (message "Testing unchanged at %d" (line-number-at-pos))
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
    (while (and (holscript-unchanged-at1) (= 0 (forward-line))))
    (should (= (point) (point-max)))))

(ert-deftest holscript-indent1A ()
  "Tests every line in sampleScript is already indented correctly"
  (holscript-fixture-in "sampleScript.sml" "w" 'holscript-eachline-unchanged))

(ert-deftest holscript-indent1B ()
  "Tests every line in sampleScript is already indented correctly"
  (holscript-fixture-in "sampleScript.sml" "_" 'holscript-eachline-unchanged))

(defun holscript-indent2-test ()
  (goto-char 86)
  (insert " \t  ")
  (indent-for-tab-command)
  (should (= (point) 86))
  (should (looking-at "^Theorem.bar:")))

(ert-deftest holscript-indent2A ()
  "Tests Theorem: syntax after Theorem=; space insert fixed (w)"
  (holscript-fixture-in "sampleScript.sml" "w" 'holscript-indent2-test))

(ert-deftest holscript-indent2B ()
  "Tests Theorem: syntax after Theorem=; space insert fixed (_)"
  (holscript-fixture-in "sampleScript.sml" "_" 'holscript-indent2-test))

(defun holscript-indent3-test ()
  (goto-char 111)
  (insert "\n")
  (indent-for-tab-command)
  (should (= (point) 114))
  (beginning-of-line)
  (should (= (point) 112))
  (should (looking-at "  simp\\[]")))
(ert-deftest holscript-indent3A ()
  "Tactic indents 2 when moved under proof keyword (w)"
  (holscript-fixture-in "sampleScript.sml" "w" 'holscript-indent3-test))
(ert-deftest holscript-indent3B ()
  "Tactic indents 2 when moved under proof keyword (_)"
  (holscript-fixture-in "sampleScript.sml" "_" 'holscript-indent3-test))

(defun holscript-indent4-test ()
  (goto-char 214)
  (insert "\n>-")
  (indent-for-tab-command)
  (beginning-of-line)
  (should (= (point) 215))
  (should (looking-at "  >-")))
(ert-deftest holscript-indent4A ()
  "Tactic indents to parent level 2, after >- (w)"
  (holscript-fixture-in "sampleScript.sml" "w" 'holscript-indent4-test))

(ert-deftest holscript-indent4B ()
  "Tactic indents to parent level 2, after >- (_)"
  (holscript-fixture-in "sampleScript.sml" "_" 'holscript-indent4-test))

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


(defun holscript-sexp-forward-test ()
  (should (save-excursion
            (and
             (move-check '(1 12 41 42 64 84 121 139
                             176 218 382 499)
                         'forward-sexp)
             (move-check '(2205 2486) 'forward-sexp)))))
(ert-deftest holscript-sexp-forward1A ()
  "sexp-forward moves correctly (w)"
  (holscript-fixture-in "sampleScript.sml" "w" 'holscript-sexp-forward-test))
(ert-deftest holscript-sexp-forward1B ()
  "sexp-forward moves correctly (_)"
  (holscript-fixture-in "sampleScript.sml" "_" 'holscript-sexp-forward-test))
