(provide 'holscript-mode)

;; font-locking and syntax


(defconst holscript-font-lock-keywords
  (list '("^\\(Theorem\\|Triviality\\)[[:space:]]+\\([A-Za-z0-9'_]+\\)[[ :]"
          (1 'holscript-theorem-syntax) (2 'holscript-thmname-syntax))
        '("^\\(Proof\\|^QED\\)\\>" . 'holscript-theorem-syntax)
        '("^\\(Definition\\|\\(?:Co\\)?Inductive\\)[[:space:]]+\\([A-Za-z0-9'_]+\\)[[ :]"
          (1 'holscript-definition-syntax) (2 'holscript-thmname-syntax))
        '("^Termination\\>\\|^End\\>" . 'holscript-definition-syntax)
        '("^Datatype\\>" . 'holscript-definition-syntax)
        '("^THEN[1L]?\\>" . 'holscript-then-syntax)
        '("[^A-Za-z0-9_']\\(THEN[1L]?\\)\\>" 1 'holscript-then-syntax)
        '("\\S.\\(>[->|]\\|\\\\\\\\\\)\\S." 1 'holscript-then-syntax)
        "^Type\\>"
        "^Overload\\>"
        (list (regexp-opt '("let" "local" "in" "end" "fun" "val" "open") 'words)
              'quote
              'holscript-smlsyntax)
        '("\\<cheat\\>" . 'holscript-cheat-face)
        '(hol-find-quoted-material 0 'holscript-quoted-material prepend)))

(defconst holscript-font-lock-defaults '(holscript-font-lock-keywords))

(defvar holscript-mode-syntax-table
  (let ((st (make-syntax-table)))
    (modify-syntax-entry ?\* ". 23n" st)
    (modify-syntax-entry ?\( "()1" st)
    (modify-syntax-entry ?\) ")(4" st)
    (modify-syntax-entry ?“ "(”" st)
    (modify-syntax-entry ?” ")“" st)
    (modify-syntax-entry ?‘ "(’" st)
    (modify-syntax-entry ?’ ")‘" st)
    (modify-syntax-entry ?\\ "\\" st)
    ;; backslash only escapes in strings but we need to have it seen
    ;; as one in general if the hol-mode isn't to get seriously
    ;; confused by script files that contain escaped quotation
    ;; characters. This despite the fact that it does cause pain in
    ;; terms such as \(x,y). x + y
    (mapc (lambda (c) (modify-syntax-entry c "w" st)) "_'")
    (mapc (lambda (c) (modify-syntax-entry c "_" st)) "$")
    (mapc (lambda (c) (modify-syntax-entry c "."  st)) ".%&+-/:<=>?@`^|!~#,;")
    st)
  "The syntax table used in `holscript-mode'.")

;; key maps

(defvar holscript-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map (kbd "`") 'holscript-dbl-backquote)
    (define-key map (kbd "<RET>") 'holscript-newline-and-relative-indent)
    ;;(define-key map "\M-f" 'forward-hol-tactic)
    ;;(define-key map "\M-b" 'backward-hol-tactic)
    ; (define-key map (kbd "C-M-<up>") 'hol-movement-backward-up-list)
    ; (define-key map (kbd "C-M-<left>") 'hol-movement-backward-sexp)
    map
    )
  "Keymap used in `holscript-mode'.")

;;; nicer editing with quotation symbols
(defun holscript-to-left-quote ()
  "Move left in the buffer to the previous “ or ‘ character."
  (interactive)
  (re-search-backward "‘\\|“"))

(defun holscript-to-right-quote ()
  "Move right in the buffer to just beyond the next ” or ’ character."
  (interactive)
  (re-search-forward "’\\|”"))

(defun holscript-dbl-backquote ()
  "Perform 'smart' insertion of Unicode quotes.

On existing quotes, toggles between ‘-’ and “-” pairs.  Otherwise, inserts a
‘-’ pair, leaving the cursor on the right quote, ready to insert text."
  (interactive)
  (cond
   ((use-region-p)
    (let ((beg (region-beginning))
          (end (region-end)))
      (goto-char end)
      (insert "’")
      (goto-char beg)
      (insert "‘")
      (backward-char 1)))
   ((looking-at "’")
    (if (= (char-before) #x2018) ; U+2018 = ‘
        (progn
          (backward-char 1)
          (delete-char 2)
          (insert "“”")
          (backward-char 1))
      (forward-char 1)))
   ((looking-at "”")
    (if (= (char-before) #x201C)  ; U+201C = “
           (progn
             (backward-char 1)
             (delete-char 2)
             (insert "‘’")
             (backward-char 1))
      (forward-char 1)))
   ((looking-at "“")
    (if (catch 'exit
          (save-mark-and-excursion
            (forward-char 1)
            (if (re-search-forward "”\\|“" nil t)
                (goto-char (match-beginning 0)))
            (if (looking-at "”")
                (progn (delete-char 1) (insert "’") (throw 'exit t))
              (throw 'exit nil))))
        (progn (delete-char 1) (insert "‘") (backward-char 1))))
   ((looking-at "‘")
    (if (catch 'exit
          (save-mark-and-excursion
            (forward-char 1)
            (if (re-search-forward "’\\|‘" nil t)
                (goto-char (match-beginning 0)))
            (if (looking-at "’")
                (progn (delete-char 1) (insert "”") (throw 'exit t))
              (throw 'exit nil))))
        (progn (delete-char 1) (insert "“") (backward-char 1))))
   (t (insert "‘’") (backward-char 1))))

(defun forward-smlsymbol (n)
  (interactive "p")
  (cond ((> n 0)
         (while (> n 0)
           (skip-syntax-forward "^.")
           (skip-syntax-forward ".")
           (setq n (- n 1))))
        ((< n 0)
         (setq n (- n))
         (setq n (- n (if (equal (skip-syntax-backward ".") 0) 0 1))))
         (while (> n 0)
           (skip-syntax-backward "^.")
           (skip-syntax-backward ".")
           (setq n (- n 1)))))

(defun is-a-then (s)
  (and s (or (string-equal s "THEN")
             (string-equal s "THENL")
             (string-equal s "QED")
             (string-equal s "val")
             (string-equal s ">-")
             (string-equal s ">>")
             (string-equal s ">|")
             (string-equal s "\\\\"))))

(defun next-hol-lexeme-terminates-tactic ()
  (forward-comment (point-max))
  (or (eobp)
      (char-equal (following-char) ?,)
      (char-equal (following-char) ?\))
      ;; (char-equal (following-char) ?=)
      (char-equal (following-char) ?\;)
      (is-a-then (word-at-point))
      (is-a-then (thing-at-point 'smlsymbol t))))

(defun previous-hol-lexeme-terminates-tactic ()
  (save-excursion
    (forward-comment (- (point)))
    (or (bobp)
        (char-equal (preceding-char) ?,)
        (char-equal (preceding-char) ?=)
        (char-equal (preceding-char) ?\;)
        (char-equal (preceding-char) ?\))
        (and (condition-case nil
                 (progn (backward-char 1) t)
                 (error nil))
             (or (is-a-then (word-at-point))
                 (is-a-then (thing-at-point 'smlsymbol t)))))))

(defun looking-at-tactic-terminator ()
  "Returns a cons-pair (x . y), with x the distance to end, and y the
   size of the terminator, or nil if there isn't one there. The x value may
   be zero, if point is immediately after the terminator."
  (interactive)
  (let ((c (following-char))
        (pc (preceding-char)))
    (cond ((char-equal c ?,) '(1 . 1))
          ((char-equal pc ?,) '(0 . 1))
          ((char-equal c ?\)) '(1 . 1))
          ((char-equal pc ?\)) '(0 . 1))
          ((char-equal c ?\]) '(1 . 1))
          ((char-equal pc ?\]) '(0 . 1))
          ((char-equal c ?\;) '(1 . 1))
          ((char-equal pc ?\;) '(0 . 1))
          ((let ((w (word-at-point)))
             (if (is-a-then w)
                 (cons
                  (- (cdr (bounds-of-thing-at-point 'word)) (point))
                  (length w))
               (let ((w (thing-at-point 'smlsymbol t)))
                 (if (is-a-then w)
                     (cons
                      (- (cdr (bounds-of-thing-at-point 'smlsymbol)) (point))
                      (length w))
                   nil))))))))

(defun looking-at-tactic-starter ()
  "Returns a cons-pair (x . y), with x the distance to end, and y the
   size of the terminator, or nil if there isn't one there. The x value may
   be zero, if point is immediately after the terminator."
  (interactive)
  (let ((c (following-char))
        (pc (preceding-char)))
    (cond ((char-equal c ?,) '(1 . 1))
          ((char-equal pc ?,) '(0 . 1))
          ((char-equal c ?\() '(1 . 1))
          ((char-equal pc ?\() '(0 . 1))
          ((char-equal c ?\[) '(1 . 1))
          ((char-equal pc ?\[) '(0 . 1))
          ((char-equal c ?\;) '(1 . 1))
          ((char-equal pc ?\;) '(0 . 1))
          ((let ((w (word-at-point)))
             (if (is-a-then w)
                 (cons
                  (- (cdr (bounds-of-thing-at-point 'word)) (point))
                  (length w))
               (let ((w (thing-at-point 'smlsymbol t)))
                 (if (is-a-then w)
                     (cons
                      (- (cdr (bounds-of-thing-at-point 'smlsymbol)) (point))
                      (length w))
                   nil))))))))


(defun forward-tactic-terminator (n)
  (interactive "^p")
  (cond ((> n 0)
         (let (c)
           (while (> n 0)
             (skip-syntax-forward " ")
             (setq c (looking-at-tactic-terminator))
             (while (or (not c) (equal (car c) 0))
               (forward-sexp)
               (skip-syntax-forward " ")
               (setq c (looking-at-tactic-terminator)))
             (forward-char (car c))
             (setq n (- n 1)))))
        ((< n 0)
         (setq n (- n))
         (let (c)
           (while (> n 0)
             (skip-syntax-backward " ")
             (setq c (looking-at-tactic-terminator))
             (while (or (not c) (equal (car c) (cdr c)))
               (condition-case nil
                   (backward-sexp)
                 (error (backward-char)))
               (skip-syntax-backward " ")
               (setq c (looking-at-tactic-terminator)))
             (backward-char (- (cdr c) (car c)))
             (setq n (- n 1)))))))

(defun forward-tactic-starter (n)
  (interactive "^p")
  (cond ((> n 0)
         (let (c)
           (while (> n 0)
             (skip-syntax-forward " ")
             (setq c (looking-at-tactic-starter))
             (while (or (not c) (equal (car c) 0))
               (forward-sexp)
               (skip-syntax-forward " ")
               (setq c (looking-at-tactic-starter)))
             (forward-char (car c))
             (setq n (- n 1)))))
        ((< n 0)
         (setq n (- n))
         (let (c)
           (while (> n 0)
             (skip-syntax-backward " ")
             (setq c (looking-at-tactic-starter))
             (while (or (not c) (equal (car c) (cdr c)))
               (condition-case nil
                   (backward-sexp)
                 (error (backward-char)))
               (skip-syntax-backward " ")
               (setq c (looking-at-tactic-starter)))
             (backward-char (- (cdr c) (car c)))
             (setq n (- n 1)))))))

(defun preceded-by-starter ()
  (save-excursion
    (backward-char)
    (thing-at-point 'tactic-starter)))
(defun forward-hol-tactic (n)
  (interactive "^p")
  (cond ((> n 0)
         (while (> n 0)
           (forward-comment (point-max))
           (while (thing-at-point 'tactic-terminator)
             (forward-tactic-terminator 1)
             (skip-syntax-forward " "))
           (while (not (thing-at-point 'tactic-terminator))
             (forward-sexp 1)
             (skip-syntax-forward " "))
           (skip-syntax-backward " ")
           (setq n (- n 1))))
        ((< n 0)
         (setq n (- n))
         (while (> n 0)
           (forward-comment (- (point)))
           (while (preceded-by-starter)
             (forward-tactic-starter -1)
             (skip-syntax-backward " "))
           (while (not (preceded-by-starter))
             (forward-sexp -1)
             (skip-syntax-backward " "))
           (skip-syntax-forward " ")
           (setq n (- n 1))))))

;;templates
(defun hol-extract-script-name (arg)
  "Return the name of the theory associated with the given filename"
(let* (
   (pos (string-match "[^/]*Script\.sml" arg)))
   (cond (pos (substring arg pos -10))
         (t "<insert theory name here>"))))

(defun hol-template-new-script-file ()
  "Inserts standard template for a HOL theory"
   (interactive)
   (insert "open HolKernel Parse boolLib bossLib;\n\nval _ = new_theory \"")
   (insert (hol-extract-script-name buffer-file-name))
   (insert "\";\n\n\n\n\nval _ = export_theory();\n\n"))

(defun hol-template-comment-star ()
   (interactive)
   (insert "\n\n")
   (insert "(******************************************************************************)\n")
   (insert "(*                                                                            *)\n")
   (insert "(*                                                                            *)\n")
   (insert "(*                                                                            *)\n")
   (insert "(******************************************************************************)\n"))

(defun hol-template-comment-minus ()
   (interactive)
   (insert "\n\n")
   (insert "(* -------------------------------------------------------------------------- *)\n")
   (insert "(*                                                                            *)\n")
   (insert "(*                                                                            *)\n")
   (insert "(*                                                                            *)\n")
   (insert "(* -------------------------------------------------------------------------- *)\n"))

(defun hol-template-comment-equal ()
   (interactive)
   (insert "\n\n")
   (insert "(* ========================================================================== *)\n")
   (insert "(*                                                                            *)\n")
   (insert "(*                                                                            *)\n")
   (insert "(*                                                                            *)\n")
   (insert "(* ========================================================================== *)\n"))

(defun hol-template-define (name)
   (interactive "sNew name: ")
   (insert "val ")
   (insert name)
   (insert "_def = Define `")
   (insert name)
   (insert " = `;\n"))

(defun hol-template-store-thm (name)
   (interactive "sTheorem name: ")
   (insert "\nTheorem ")
   (insert name)
   (insert ":\n\nProof\nQED\n"))

(defun hol-template-hol-relnish (style name)
  (insert (format "\n%s %s:\n  ...\nEnd\n" style name)))

(defun hol-template-hol-reln (name)
  (interactive "sConstant name: ")
  (hol-template-hol-relnish "Inductive" name))

(defun hol-template-hol-coreln (name)
  (interactive "sConstant name: ")
  (hol-template-hol-relnish "CoInductive" name))

(defun hol-template-new-datatype ()
   (interactive)
   (insert "val _ = Datatype `TREE = LEAF ('a -> num) | BRANCH TREE TREE`;\n"))

;;checking for trouble with names in store_thm, save_thm, Define
(setq store-thm-regexp
   "val[ \t\n]*\\([^ \t\n]*\\)[ \t\n]*=[ \t\n]*store_thm[ \t\n]*([ \t\n]*\"\\([^\"]*\\)\"")
(setq save-thm-regexp
   "val[ \t\n]*\\([^ \t\n]*\\)[ \t\n]*=[ \t\n]*save_thm[ \t\n]*([ \t\n]*\"\\([^\"]*\\)\"")
(setq define-thm-regexp
   "val[ \t\n]*\\([^ \t\n]*\\)_def[ \t\n]*=[ \t\n]*Define[ \t\n]*`[ \t\n(]*\$?\\([^ \t\n([!?:]*\\)")

(setq statement-eq-regexp-list (list store-thm-regexp save-thm-regexp define-thm-regexp))

(defun hol-correct-eqstring (s1 p1 s2 p2)
  (interactive)
  (let (choice)
    (setq choice 0)
    (while (eq choice 0)
      (message
       (concat
	"Different names used. Please choose one:\n(0) "
	s1 "\n(1) " s2 "\n(i) ignore"))
      (setq choice (if (fboundp 'read-char-exclusive)
		       (read-char-exclusive)
		     (read-char)))
      (cond ((= choice ?0) t)
	    ((= choice ?1) t)
	    ((= choice ?i) t)
	    (t (progn (setq choice 0) (ding))))
      )
    (if (= choice ?i) t
    (let (so sr pr)
      (cond ((= choice ?0) (setq so s1 sr s2 pr p2))
	    (t             (setq so s2 sr s1 pr p1)))
      (delete-region pr (+ pr (length sr)))
      (goto-char pr)
      (insert so)
      ))))


(defun hol-check-statement-eq-string ()
  (interactive)
  (save-excursion
  (dolist (current-regexp statement-eq-regexp-list t)
  (goto-char 0)
  (let (no-error-found s1 p1 s2 p2)
    (while (re-search-forward current-regexp nil t)
      (progn (setq s1 (match-string-no-properties 1))
             (setq s2 (match-string-no-properties 2))
             (setq p1 (match-beginning 1))
             (setq p2 (match-beginning 2))
             (setq no-error-found (string= s1 s2))
             (if no-error-found t (hol-correct-eqstring s1 p1 s2 p2)))))
  (message "checking for problematic names done"))))

;; make newline do a newline and relative indent
(defun holscript-newline-and-relative-indent ()
  "Insert a newline, then perform a `relative indent'."
  (interactive "*")
  (delete-horizontal-space t)
  (let ((doindent (save-excursion (forward-line 0)
                                  (equal (char-syntax (following-char)) ?\s))))
    (newline nil t)
    (if doindent (indent-relative))))

;;indentation and other cleanups
(defun hol-replace-tabs-with-spaces ()
   (save-excursion
      (goto-char (point-min))
      (while (search-forward "\t" nil t)
         (delete-region (- (point) 1) (point))
         (let* ((count (- tab-width (mod (current-column) tab-width))))
           (dotimes (i count) (insert " "))))))

(defun hol-remove-tailing-whitespaces ()
   (save-excursion
      (goto-char (point-min))
      (while (re-search-forward " +$" nil t)
         (delete-region (match-beginning 0) (match-end 0)))))


(defun hol-remove-tailing-empty-lines ()
   (save-excursion
      (goto-char (point-max))
      (while (bolp) (delete-char -1))
      (insert "\n")))

(defun hol-cleanup-buffer ()
   (interactive)
   (hol-replace-tabs-with-spaces)
   (hol-remove-tailing-whitespaces)
   (hol-remove-tailing-empty-lines)
   (message "Buffer cleaned up!"))

;;replace common unicode chars with ascii version
(setq hol-unicode-replacements '(
  (nil "¬" "~")
  (nil "∧" "/\\\\")
  (nil "∨" "\\\\/")
  (nil "⇒" "==>")
  (nil "⇔" "<=>")
  (nil "⇎" "<=/=>")
  (nil "≠" "<>")
  (nil "∃" "?")
  (nil "∀" "!")
  (nil "λ" "\\\\")
  (nil "“" "``")
  (nil "”" "``")
  (nil "‘" "`")
  (nil "’" "`")
  (t "∈" "IN")
  (t "∉" "NOTIN")
  (nil "α" "'a")
  (nil "β" "'b")
  (nil "γ" "'c")
  (nil "δ" "'d")
  (nil "ε" "'e")
  (nil "ζ" "'f")
  (nil "η" "'g")
  (nil "θ" "'h")
  (nil "ι" "'i")
  (nil "κ" "'j")
  (nil "μ" "'l")
  (nil "ν" "'m")
  (nil "ξ" "'n")
  (nil "ο" "'o")
  (nil "π" "'p")
  (nil "ρ" "'q")
  (nil "ς" "'r")
  (nil "σ" "'s")
  (nil "τ" "'t")
  (nil "υ" "'u")
  (nil "φ" "'v")
  (nil "χ" "'w")
  (nil "ψ" "'x")
  (nil "ω" "'y")
  (t "≤₊" "<=+")
  (t ">₊" ">+")
  (t "<₊" "<+")
  (t "≥₊" ">=+")
  (t "≤" "<=")
  (t "≥" ">=")
  (nil "⁺" "^+")
  (t "∅ᵣ" "EMPTY_REL")
  (t "𝕌ᵣ" "RUNIV")
  (t "⊆ᵣ" "RSUBSET")
  (t "∪ᵣ" "RUNION")
  (t "∩ᵣ" "RINTER")
  (t "∅" "{}")
  (nil "𝕌" "univ")
  (t "⊆" "SUBSET")
  (t "∪" "UNION")
  (t "∩" "INTER")
  (t "⊕" "??")
  (t "‖" "||")
  (t "≪" "<<")
  (t "≫" ">>")
  (t "⋙" ">>>")
  (t "⇄" "#>>")
  (t "⇆" "#<<")
  (t "∘" "o")
  (t "∘ᵣ" "O")
  (t "−" "-")
))


(defun replace-string-in-buffer (s_old s_new)
   (save-excursion
      (goto-char (point-min))
      (while (search-forward s_old nil t)
         (replace-match s_new))))

(defun replace-string-in-buffer_ensure_ws (s_old s_new)
  (replace-string-in-buffer (concat " " s_old " ") (concat " " s_new " "))
  (replace-string-in-buffer (concat s_old " ") (concat " " s_new " "))
  (replace-string-in-buffer (concat " " s_old) (concat " " s_new " "))
  (replace-string-in-buffer s_old (concat " " s_new " "))
)

(defun hol-remove-unicode ()
  (interactive)
  (save-excursion
    (save-restriction
      (if (use-region-p) (narrow-to-region (region-beginning) (region-end)))
      (dolist (elt hol-unicode-replacements)
        (if (nth 0 elt)
          (replace-string-in-buffer_ensure_ws (nth 1 elt) (nth 2 elt))
          (replace-string-in-buffer (nth 1 elt) (nth 2 elt))
          )))))

(defun hol-fl-extend-region ()
  (let ((newbeg (hol-fl-term-bump-backwards font-lock-beg))
        (newend (hol-fl-term-bump-forwards font-lock-end))
        (changed nil))
    (if (= newbeg font-lock-beg) nil
      (setq font-lock-beg newbeg)
      (setq changed t))
    (if (= newend font-lock-end) nil
      (setq font-lock-end newend)
      (setq changed t))
    changed))

(defun hol-movement-in-proof-p (pos)
  (save-excursion
    (goto-char pos)
    (let ((pp (syntax-ppss)))
      (and (not (nth 3 pp)) (not (nth 4 pp))
           (let ((nextre (re-search-backward hol-proof-beginend-re nil t)))
             (and nextre
                  (let ((s (match-string-no-properties 0)))
                    (and (not (equal s "QED")) (not (equal s "End"))
                         (match-beginning 0)))))))))

(defun hol-movement-backward-up-list
    (&optional n escape-strings no-syntax-crossing)
  (interactive "^p\nd\nd")
  (or (let ((p (hol-movement-in-proof-p (point)))) (and p (goto-char p)))
      (and (looking-at "^Proof\\>")
           (re-search-backward "^\\(Triviality\\>\\|Theorem\\>\\)" nil t))
      (and (looking-at "^Termination\\>")
           (re-search-backward "^Definition\\>" nil t))
      (backward-up-list n escape-strings no-syntax-crossing)))

(defconst hol-movement-top-re
  "^\\(Theorem\\|Triviality\\|Definition\\|Datatype\\|Overload\\|Type\\)")
(defun hol-movement-backward-sexp (&optional arg)
  (interactive "p")
  (if (and (> arg 0)
           (save-excursion
             (beginning-of-line)
             (looking-at hol-movement-top-re)))
      (progn
        (re-search-backward hol-movement-top-re nil t)
        (hol-movement-backward-sexp (1- arg)))
    (backward-sexp arg)))

(defun holscript-fix-quotations (start end)
  (interactive "r")
  (shell-command-on-region start end
                           (concat (file-name-directory hol-executable)
                                   "unquote --quotefix")
                           nil
                           t))

(defun holscript-mode-variables ()
  (set-syntax-table holscript-mode-syntax-table)
  (setq local-abbrev-table holscript-mode-abbrev-table)
  (smie-setup holscript-smie-grammar #'holscript-smie-rules
              :backward-token #'holscript-smie-backward-token
              :forward-token #'holscript-smie-forward-token)
  (set (make-local-variable 'parse-sexp-ignore-comments) t)
  (set (make-local-variable 'comment-start) "(* ")
  (set (make-local-variable 'comment-end) " *)")
  (set (make-local-variable 'comment-start-skip) "(\\*+\\s-*")
  (set (make-local-variable 'comment-end-skip) "\\s-*\\*+)")
  ;; No need to quote nested comments markers.
  (set (make-local-variable 'comment-quote-nested) nil))

(defun holscript-indent-line () (indent-relative t))

(define-derived-mode holscript-mode prog-mode "HOLscript"
  "\\<holscript-mode-map>Major mode for editing HOL Script.sml files.

\\{sml-mode-map}"
  (setq font-lock-multiline t)
  (if (member 'hol-fl-extend-region font-lock-extend-region-functions) nil
    (setq font-lock-extend-region-functions
          (append font-lock-extend-region-functions
                  '(hol-fl-extend-region))))
  (set (make-local-variable 'font-lock-defaults) holscript-font-lock-defaults)
  (set (make-local-variable 'indent-tabs-mode) nil)
  (set (make-local-variable 'indent-line-function) 'holscript-indent-line)
  (holscript-mode-variables)
)

(require 'hol-input)
(add-hook 'holscript-mode-hook (lambda () (set-input-method "Hol")))

;; smie grammar

(require 'smie)
(defvar holscript-smie-grammar
  (smie-prec2->grammar
   (smie-bnf->prec2
    '((id)
      (decls (decls ";" decls) (decl))
      (decl ("^Theorem" theorem-contents "^QED")
            ("^Triviality" theorem-contents "^QED")
            ("^Theorem=" id)
            ("^Triviality=" id)
            ("^Definition" definition-contents "^End")
            ("^Inductive" id-quoted "^End")
            ("^CoInductive" id-quoted "^End")
            ("^Overload" id)
            ("^Type" id)
            ("^Datatype" quotedmaterial "^End")
            ("val" id)
            ("fun" id)
            ("open" id)
            ("datatype" id)
            ("structure" id))
      (theorem-contents (id-quoted "^Proof" tactic))
      (definition-contents (id-quoted "^Termination" tactic) (id-quoted))
      (id-quoted (id ":" quotedmaterial))
      (quotedmaterial
        ("QFIER." quotedmaterial "ENDQ." quotedmaterial)
        (quotedmaterial "/\\" quotedmaterial)
        (quotedmaterial "∧" quotedmaterial)
        (quotedmaterial "\\/" quotedmaterial)
        (quotedmaterial "∨" quotedmaterial)
        (quotedmaterial "<=>" quotedmaterial)
        (quotedmaterial "⇔" quotedmaterial)
        (quotedmaterial "==>" quotedmaterial)
        (quotedmaterial "⇒" quotedmaterial)
        (quotedmaterial "=" quotedmaterial)
        (quotedmaterial "<" quotedmaterial)
        (quotedmaterial "≤" quotedmaterial)
        (quotedmaterial "<=" quotedmaterial)
        (quotedmaterial "+" quotedmaterial)
        (quotedmaterial "*" quotedmaterial)
        (quotedmaterial ":=" quotedmaterial)
        (quotedmaterial "<-" quotedmaterial)
        (quotedmaterial "|" quotedmaterial)
        (quotedmaterial "=>" quotedmaterial)
        ("case" quotedmaterial "of" quotedmaterial)
        ("do" quotedmaterial "od")
        ("if" quotedmaterial "then" quotedmaterial "else" quotedmaterial)
        ("let" quotedmaterial "in" quotedmaterial)
        ("<|" recd-fields "|>"))
      (recd-fields (recd-fields ";" recd-fields) (quotedmaterial))
      (quotation ("‘" quotedmaterial "’"))
      (termtype ("“" quotedmaterial "”"))
      (tactic (tactic ">>" tactic)
              (tactic "\\\\" tactic)
              (tactic ">-" tactic)
              (tactic ">|" tactic)
              (tactic "THEN" tactic)
              (tactic "THEN1" tactic)
              (tactic "THENL" tactic)
              (quotation "by" tactic)
              (quotation "suffices_by" tactic)
              ("[" tactics "]"))
      (tactics (tactic) (tactics "," tactics)))
    '((assoc ",")) '((assoc ";"))
    '((assoc "^Proof")
      (assoc ">>" "\\\\" ">-"  ">|" "THEN" "THEN1" "THENL")
      (assoc "by" "suffices_by"))
    '((assoc "ENDQ." "QFIER." "in" "of")
      (assoc "|")
      (assoc "=>")
      (assoc "else")
      (assoc "<=>" "⇔" "<-")
      (assoc "==>" "⇒") (assoc "\\/" "∨") (assoc "/\\" "∧")
      (assoc "=" "<" "≤" "<=") (assoc ":=") (assoc "+") (assoc "*")))))

(defconst holscript-quoteddeclaration-begin
  (concat
   "^\\(Theorem\\|Triviality\\|Definition\\|Inductive\\|CoInductive\\)"
   "[[:space:]]+\\([A-Za-z0-9'_]+\\)[[:space:]]*" ; name
   "\\(\\[[A-Za-z0-9'_,]+\\]\\)?[[:space:]]*:"; optional annotations)
  "Regular expression marking the beginning of the special syntax that marks
a store_thm equivalent."))

(defconst holscript-quoteddeclaration-end
  (regexp-opt (list "End" "Proof" "Termination")))

(defvar holscript-quotedmaterial-delimiter-regexp
  (regexp-opt (list "“" "”" "‘" "’" holscript-quoteddeclaration-begin)))

(defvar holscript-boolean-quantifiers '("?" "!" "?!" "∀" "∃" "∃!"))

(defvar holscript-quantifier-regexp
  (concat (regexp-opt holscript-boolean-quantifiers) "\\|"
          (regexp-opt '("some" "LEAST") 'words) "\\|[@λ]")
  "List of strings that can begin \"quantifier blocks\".")


(defun holscript-can-find-earlier-quantifier (pp)
  (let* ((pstk (nth 9 pp))
         (limit (car (last pstk))))
    (save-mark-and-excursion
      (catch 'found-one
        (while (re-search-backward
                (concat "\\(" holscript-quoteddeclaration-begin "\\)" "\\|"
                        "\\(" holscript-quoteddeclaration-end "\\)" "\\|"
                        holscript-quotedmaterial-delimiter-regexp "\\|"
                        holscript-quantifier-regexp "\\|\\.")
                limit
                t)
          (let ((pp1 (syntax-ppss)))
            (if (or (nth 3 pp1) (nth 4 pp1))
                (goto-char (nth 8 pp1))
              (if (equal (car (last (nth 9 pp1))) limit)
                  (if (looking-at holscript-quantifier-regexp)
                      (throw 'found-one (point))
                    (throw 'found-one nil))))))))))

(defconst holscript-column0-keywords-regexp
  (regexp-opt '("Definition" "Datatype" "Theorem" "Triviality" "Type"
                "Proof"
                "Termination" "End" "QED" "Inductive" "CoInductive"
                "Overload")))
(defconst holscript-column0-declbegin-keyword
  (regexp-opt '("Definition" "Datatype" "Theorem" "Triviality"
                "Type" "Inductive" "CoInductive" "Overload")))

(defconst holscript-sml-declaration-keyword
  (regexp-opt '("open" "val" "datatype" "local" "fun" "infix" "infixl" "infixr"
                "structure" "signature" "functor") 'words))

(defun holscript-simple-token-forward ()
  (let* ((p (point))
         (sc (syntax-class (syntax-after p))))
    (cond
     ((or (equal 1 sc) (equal 9 sc)); punctuation
      (skip-syntax-forward ".\\")
      (buffer-substring-no-properties p (point)))
     ((equal 2 sc) ; word
      (skip-syntax-forward "w")
      (buffer-substring-no-properties p (point))))))

(defun holscript-simple-token-backward ()
  (let* ((p (point))
         (sc (syntax-class (syntax-after (1- p)))))
    (cond
     ((or (equal 1 sc) (equal 9 sc)); punctuation
      (skip-syntax-backward ".\\")
      (buffer-substring-no-properties (point) p))
     ((equal 2 sc) ; word
      (skip-syntax-backward "w")
      (buffer-substring-no-properties (point) p)))))


(defun holscript-smie-forward-token ()
  (let ((p0 (point)))
    (forward-comment (point-max))
    (if (and (not (= p0 (point)))
             (or (looking-at
                  (concat holscript-column0-declbegin-keyword "[[:space:]]"))
                 (looking-at (concat "^" holscript-sml-declaration-keyword))))
        ";"
      (let ((pp (syntax-ppss)))
        (cond
         ((and (looking-at (concat "\\(" holscript-column0-keywords-regexp
                                   "\\)" "[[:space:]]"))
               (save-excursion (skip-chars-backward " \t") (bolp)))
          (goto-char (match-end 1))
          (let ((ms (match-string-no-properties 1)))
            (if (or (string= ms "Theorem") (string= ms "Triviality"))
                (let ((eolpoint (save-excursion (end-of-line) (point))))
                  (save-excursion
                    (if (re-search-forward ":" eolpoint t) (concat "^" ms)
                      (concat "^" ms "="))))
              (concat "^" ms))))
         ((looking-at holscript-quotedmaterial-delimiter-regexp)
          (goto-char (match-end 0))
          (match-string-no-properties 0))
         ((looking-at "\\\\/") (goto-char (match-end 0)) "\\/")
         ((looking-at "/\\\\") (goto-char (match-end 0)) "/\\")
         ((looking-at "\\.")
          (if (or (nth 3 pp) (nth 4 pp))
              (progn (forward-char 1) ".")
            (let ((tok
                   (if (holscript-can-find-earlier-quantifier pp) "ENDQ."
                     ".")))
              (forward-char 1) tok)))
         ((looking-at holscript-quantifier-regexp)
          (goto-char (match-end 0)) "QFIER.")
         ((equal 1 (syntax-class (syntax-after (point))))
          (buffer-substring-no-properties
           (point)
           (progn (skip-syntax-forward ".") (point))))
         ((looking-at "\\$")
          (let ((p (point)))
            (if (> (skip-chars-forward "$") 1)
                (buffer-substring-no-properties p (point))
              (let ((simple-tok (holscript-simple-token-forward)))
                (if (null simple-tok)
                    "$"
                  (if (= 1  ; punctuation, so don't look for more
                         (syntax-class
                          (aref (syntax-table) (aref simple-tok 0))))
                      (buffer-substring-no-properties p (point))
                    (if (looking-at "\\$")
                        (progn (forward-char 1)
                               (holscript-simple-token-forward)))
                    (buffer-substring-no-properties p (point))))))))
         (t (let ((p (point)))
              (skip-syntax-forward "w")
              (if (looking-at "\\$")
                  (progn (forward-char 1)
                         (holscript-simple-token-forward)))
              (buffer-substring-no-properties p (point)))))))))

(defun holscript-smie-backward-token ()
  (if (or (and (looking-at
                (concat holscript-column0-declbegin-keyword "[[:space:]]"))
               (save-excursion (skip-chars-backward " \t") (bolp)))
          (looking-at (concat "^" holscript-sml-declaration-keyword)))
      (if (= (point) (point-min)) ""
        (skip-syntax-backward " ")
        ";")
    (let ((cp (point)))
      (forward-comment (- (point)))
      (skip-syntax-backward " ")
      (while (not (equal cp (point)))
        (setq cp (point))
        (forward-comment (- (point)))
        (skip-syntax-backward " ")))
    (cond
     (; am I just after a keyword?
      (and (looking-back holscript-column0-keywords-regexp (- (point) 15) t)
           (let ((syn (syntax-after (point))))
             (or (null syn) (= 0 (car syn)))) ; next char is whitespace
           (save-excursion
             (goto-char (match-beginning 0))
             (skip-chars-backward " \t")
             (bolp)))
      (goto-char (match-beginning 0))
      (let ((ms (match-string-no-properties 0)))
        (if (or (string=  ms "Theorem") (string= ms "Triviality"))
            (let ((eolpoint (save-excursion (end-of-line) (point))))
              (save-excursion
                (if (re-search-forward ":" eolpoint t) (concat "^" ms)
                  (concat "^" ms "="))))
          (concat "^" ms))))
     (; am I just after a quotation mark
      (looking-back holscript-quotedmaterial-delimiter-regexp (- (point) 1) t)
      (goto-char (match-beginning 0))
      (match-string-no-properties 0))
     (; am I just after a quantifier
      (looking-back holscript-quantifier-regexp (- (point) 10) t)
      (goto-char (match-beginning 0))
      (let ((c (char-before)))
        (if (and c (char-equal c ?$))
            (progn (backward-char) (concat "$" (match-string-no-properties 0)))
          "QFIER.")))
     (; am I sitting on a full-stop that might end a quantifier block
      (let ((c (char-before))) (and c (char-equal c ?.)))
      (forward-char -1)
      (let* ((pp (syntax-ppss)))
        (if (or (nth 3 pp) (nth 4 pp)) "."
          (if (holscript-can-find-earlier-quantifier pp) "ENDQ." "."))))
     ((looking-back "\\\\/" (- (point) 3))
      (goto-char (match-beginning 0)) "\\/")
     ((looking-back "/\\\\" (- (point) 3))
      (goto-char (match-beginning 0)) "/\\")
     (; am I sitting after "punctuation"
      (equal 1 (syntax-class (syntax-after (1- (point)))))
      (buffer-substring-no-properties
       (point)
       (progn (skip-syntax-backward ".") (point))))
     (t (buffer-substring-no-properties
         (point)
         (progn (skip-syntax-backward "w_")
                (point)))))))

(defvar holscript-indent-level 0 "Default indentation level")
(defun holscript-smie-rules (kind token)
  (message "in smie rules, looking at (%s,>%s<)" kind token)
  (pcase (cons kind token)
    (`(:elem  . basic) (progn (message "In elem rule")
                              holscript-indent-level))
    (`(:list-intro . ":") (message "In list-intro :") holscript-indent-level)
    (`(:list-intro . "‘") 1)
    (`(:list-intro . "“") 1)
    (`(:list-intro . "")
     (message "In (:list-intro \"\"))") holscript-indent-level)
    (`(:after . ":") 2)
    (`(:before . "^CoInductive") '(column . 0))
    (`(:before . "^Definition") '(column . 0))
    (`(:before . "^Inductive") '(column . 0))
    (`(:before . "^Proof") '(column . 0))
    (`(:before . "^QED") '(column . 0))
    (`(:before . "^Termination") '(column . 0))
    (`(:before . "^Theorem") '(column . 0))
    (`(:before . "^Theorem=") '(column . 0))
    (`(:after . "^Proof") 2)
    (`(:after . "^Termination") 2)
    (`(:before . "val") 0)
    (`(:before . "fun") 0)
    (`(:before . "open") 0)
    (`(:before . "ENDQ.") 0)
    (`(:after . "ENDQ.") 2)
    (`(:after . ";") 0)
    (`(:after . "let") 2)
    (`(:after . "in") 2)
    (`(:after . "then") 2)
    (`(:after . "else") 2)
    (`(:after . "of") (if (smie-rule-next-p "|") 0 2))
    (`(:before . "|") (if (smie-rule-parent-p "of") 0))
    (`(:before ."if")
     (and (not (smie-rule-bolp))
          (smie-rule-prev-p "else")
          (smie-rule-parent)))
    (`(:before . ":") holscript-indent-level)
    (`(:after . "=>") 2)
    (`(:after . "do") 2)
    ; (`(:before . "==>") 2)
    ; (`(:before . "⇒") 2)
    (`(:before . "by")  (cond ((smie-rule-parent-p "^Proof") 4)
                                      ((smie-rule-parent-p "(" "[") 3)
                                      (t 2)))
    (`(:before . "suffices_by") (cond ((smie-rule-parent-p "^Proof") 4)
                                      ((smie-rule-parent-p "(" "[") 3)
                                      (t 2)))
    (`(:close-all . _) t)
    (`(:after . "[") 2)
    (`(:after . "<|") 2)
    (`(:after . ">-") 1)
    (`(:after . "‘") 1)
    (`(:after . "“") 1)
    (`(:after . "THEN1") 1)
))

;;; returns true and moves forward a sexp if this is possible, returns nil
;;; and stays where it is otherwise
(defun my-forward-sexp ()
  (condition-case nil
      (progn (forward-sexp 1) t)
    (error nil)))
(defun my-backward-sexp()
  (condition-case nil
      (progn (backward-sexp 1) t)
    (error nil)))

(defun word-before-point ()
  (save-excursion
    (condition-case nil
        (progn (backward-char 1) (word-at-point))
      (error nil))))

(defun backward-hol-tactic (n)
  (interactive "p")
  (forward-hol-tactic (if n (- n) -1)))

(defun prim-mark-hol-tactic ()
  (let ((bounds (bounds-of-thing-at-point 'hol-tactic)))
    (if bounds
        (progn
          (goto-char (cdr bounds))
          (push-mark (car bounds) t t)
          (set-region-active))
      (error "No tactic at point"))))

(defun mark-hol-tactic ()
  (interactive)
  (let ((initial-point (point)))
    (condition-case nil
        (prim-mark-hol-tactic)
      (error
       ;; otherwise, skip white-space forward to see if this would move us
       ;; onto a tactic.  If so, great, otherwise, go backwards and look for
       ;; one there.  Only if all this fails signal an error.
       (condition-case nil
           (progn
             (skip-chars-forward " \n\t\r")
             (prim-mark-hol-tactic))
         (error
          (condition-case e
              (progn
                (if (skip-chars-backward " \n\t\r")
                    (progn
                      (backward-char 1)
                      (prim-mark-hol-tactic))
                  (prim-mark-hol-tactic)))
            (error
             (goto-char initial-point)
             (signal (car e) (cdr e))))))))))

;; face info for syntax
(defface holscript-theorem-syntax
  '((((class color)) :foreground "blueviolet"))
  "The face for highlighting script file Theorem-Proof-QED syntax."
  :group 'holscript-faces)

(defface holscript-thmname-syntax
  '((((class color)) :weight bold))
    "The face for highlighting theorem names."
    :group 'holscript-faces)

(defface holscript-cheat-face
  '((((class color)) :foreground "orange" :weight ultra-bold :box t))
  "The face for highlighting occurrences of the cheat tactic."
  :group 'holscript-faces)

(defface holscript-definition-syntax
  '((((class color)) :foreground "indianred"))
  "The face for highlighting script file definition syntax."
  :group 'holscript-faces)

(defface holscript-quoted-material
  '((((class color)) :foreground "brown" :weight bold))
  "The face for highlighting quoted material."
  :group 'holscript-faces)

(defface holscript-then-syntax
  '((((class color)) :foreground "DarkSlateGray4" :weight bold))
  "The face for highlighting `THEN' connectives in tactics."
  :group 'holscript-faces)

(defface holscript-smlsyntax
  '((((class color)) :foreground "DarkOliveGreen" :weight bold))
  "The face for highlighting important SML syntax that appears in script files."
  :group 'holscript-faces)

(setq auto-mode-alist (cons '("Script\\.sml" . holscript-mode)
                            auto-mode-alist))
