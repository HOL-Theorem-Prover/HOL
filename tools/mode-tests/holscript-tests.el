;;; run with something like
;;;  HOLDIR=<dir> emacs -batch -l ert -l holscript-tests.el -f ert-run-tests-batch-and-exit

(load (concat (file-name-as-directory (getenv "HOLDIR")) "tools/hol-mode"))

(defun holscript-fixture-in (file body)
  (with-temp-buffer
    (insert-file-contents-literally (concat holdir "tools/mode-tests/" file))
    (holscript-mode)
    (set-buffer-modified-p nil)
    (funcall body)))


(defun holscript-unchanged-at1 ()
  (let ((p (point)))
    (indent-for-tab-command)
    (not (buffer-modified-p))))

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
    (not (= (forward-line) 0))))

(ert-deftest holscript-indent1 ()
  "Tests Theorem: syntax after Theorem=; no need for change"
  (holscript-fixture-in "sampleScript.sml" 'holscript-eachline-unchanged))

(ert-deftest holscript-indent2 ()
  "Tests Theorem: syntax after Theorem=; space insert fixed"
  (holscript-fixture-in "sampleScript.sml"
                        (lambda ()
                          (goto-char 86)
                          (insert " \t  ")
                          (indent-for-tab-command)
                          (should (= (point) 86))
                          (should (looking-at "^Theorem.bar:")))))

(ert-deftest holscript-indent3 ()
  "Tactic indents 2 when moved under proof keyword"
  (holscript-fixture-in
   "sampleScript.sml"
   (lambda ()
     (goto-char 111)
     (insert "\n")
     (indent-for-tab-command)
     (should (= (point) 114))
     (beginning-of-line)
     (should (= (point) 112))
     (should (looking-at "  simp\\[]")))))

(ert-deftest holscript-indent4 ()
  "Tactic indents to parent level 2, after >-"
  (holscript-fixture-in
   "sampleScript.sml"
   (lambda()
     (goto-char 214)
     (insert "\n>-")
     (indent-for-tab-command)
     (beginning-of-line)
     (should (= (point) 215))
     (should (looking-at "  >-")))))
