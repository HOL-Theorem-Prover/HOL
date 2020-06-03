;;; run with something like
;;;  HOLDIR=<dir> emacs -batch -l ert -l holscript-tests.el -f ert-run-tests-batch-and-exit

(load (concat (file-name-as-directory (getenv "HOLDIR")) "tools/hol-mode"))

(defun holscript-fixture-in (file sword-arg body)
  (with-temp-buffer
    (insert-file-contents-literally (concat holdir "tools/mode-tests/" file))
    (decode-coding-region (point-min) (point-max) 'utf-8-unix)
    (holscript-mode)
    (set-buffer-modified-p nil)
    (superword-mode sword-arg)
    (funcall body)))

(defun holscript-fixture-both (file body)
  (holscript-fixture-in file 0 body)
  (holscript-fixture-in file 1 body))


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

(ert-deftest holscript-indent1 ()
  "Tests every line in sampleScript is already indented correctly"
  (holscript-fixture-both "sampleScript.sml" 'holscript-eachline-unchanged))

(defun holscript-indent2-test ()
  (goto-char 86)
  (insert " \t  ")
  (indent-for-tab-command)
  (should (= (point) 86))
  (should (looking-at "^Theorem.bar:")))

(ert-deftest holscript-indent2 ()
  "Tests Theorem: syntax after Theorem="
  (holscript-fixture-both "sampleScript.sml" 'holscript-indent2-test))

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
  (holscript-fixture-both "sampleScript.sml" 'holscript-indent3-test))


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


(defun holscript-sexp-forward-test ()
  (should (save-excursion
            (and
             (move-check '(1 12 41 42 64 84 121 139
                             176 218 382 499)
                         'forward-sexp)
             (move-check '(2205 2486) 'forward-sexp)))))
(ert-deftest holscript-sexp-forward1 ()
  "sexp-forward moves correctly"
  (holscript-fixture-both "sampleScript.sml" 'holscript-sexp-forward-test))
