(provide 'holscript-mode)

;; font-locking and syntax

(defvar holscript-definitionlabel-re
  "\\(\\[~?[A-Za-z0-9_']+\\(\\[[A-Za-z0-9_',]+\\]\\)?[[:space:]]*:[[:space:]]*\\]\\)\\|\\[\\(/\\\\\\|∧\\)\\]\\|^\\[\\]"
  "Regular expression for case-labels occurring within HOL definitions,
ignoring fact that it should really only occur at the beginning of the line.")

(defconst holscript-font-lock-keywords
  (list '("^\\(Theorem\\|Triviality\\|Resume\\)[[:space:]]+\\([A-Za-z0-9'_]+\\)[[ :]"
          (1 'holscript-theorem-syntax) (2 'holscript-thmname-syntax))
        '("^\\(Finalise\\)[[:space:]]+\\([A-Za-z0-9'_]+\\)"
          (1 'holscript-theorem-syntax) (2 'holscript-thmname-syntax))
        '("^\\(Theory\\)[[:space:]]+\\([A-Za-z0-9'_]+\\)[[:space:]]*"
          (1 'holscript-theorem-syntax) (2 'holscript-thmname-syntax))
        '("^\\(Ancestors\\|Libs\\)\\_>" . 'holscript-theorem-syntax)
        '("^\\(Proof\\|^QED\\)\\>" . 'holscript-theorem-syntax)
        '("^\\(Definition\\|\\(?:Co\\)?Inductive\\)[[:space:]]+\\([A-Za-z0-9'_]+\\)[[ :]"
          (1 'holscript-definition-syntax) (2 'holscript-thmname-syntax))
        '("^\\(Quote\\)[[:space:]]+\\([A-Za-z0-9'_]+\\)[[:space:]]*=[[:space:]]*\\([A-Za-z0-9'_.]+\\)[[:space:]]*:"
          (1 'holscript-definition-syntax) (2 'holscript-thmname-syntax)
          (3 'holscript-thmname-syntax))
        '("^\\(Quote\\)[[:space:]]+\\([A-Za-z0-9'_.]+\\)[[:space:]]*:"
          (1 'holscript-definition-syntax) (2 'holscript-thmname-syntax))
        '("^Termination\\>\\|^End\\>" . 'holscript-definition-syntax)
        '("^\\(Datatype\\)[[:space:]]*:" (1 'holscript-definition-syntax))
        '("\\_<THEN\\_>" . 'holscript-then-syntax)
        '("\\_<THEN1\\_>" . 'holscript-then-syntax)
        '("\\_<THENL\\_>" . 'holscript-then-syntax)
        '("\\_<THEN_LT\\_>" . 'holscript-then-syntax)
        '("\\S.\\(>\\(>>?\\|[-~|]\\)\\|\\\\\\\\\\)\\S." 1
          'holscript-then-syntax)
        '("\\S.\\(>>~-\\)\\S." 1 'holscript-then-syntax)
        "^Type\\>"
        "^Overload\\>"
        (list (regexp-opt
               '("let" "local" "in" "end" "fun" "val" "open")
               'symbols)
              'quote
              'holscript-smlsyntax)
        '("\\<cheat\\>" . 'holscript-cheat-face)
        '(holscript-find-syntax-error 0 'holscript-syntax-error-face prepend)
        '(hol-find-quoted-material 0 'holscript-quoted-material prepend)
        (list
         holscript-definitionlabel-re 0
          (quote 'holscript-definition-label-face) 'prepend)))

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
    (modify-syntax-entry ?λ "." st)
    (modify-syntax-entry ?⁺ "." st)
    (modify-syntax-entry ?꙳ "." st)
    (modify-syntax-entry ?⁼ "." st)
    (modify-syntax-entry ?⁻ "." st)
    (modify-syntax-entry ?` "$" st)
    ;; backslash only escapes in strings but we need to have it seen
    ;; as one in general if the hol-mode isn't to get seriously
    ;; confused by script files that contain escaped quotation
    ;; characters. This despite the fact that it does cause pain in
    ;; terms such as \(x,y). x + y
    (mapc (lambda (c) (modify-syntax-entry c "w" st)) "'")
    (mapc (lambda (c) (modify-syntax-entry c "_" st)) "$_")
    (mapc (lambda (c) (modify-syntax-entry c "."  st)) ".%&+-/:<=>?@^|!~#,;∀∃")
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
         (setq n (- n (if (equal (skip-syntax-backward ".") 0) 0 1)))
         (while (> n 0)
           (skip-syntax-backward "^.")
           (skip-syntax-backward ".")
           (setq n (- n 1))))))

(defun is-a-then (s)
  (and s (or (string-equal s "THEN")
             (string-equal s "THEN_LT")
             (string-equal s "THENL")
             (string-equal s "QED")
             (string-equal s "val")
             (string-equal s ">-")
             (string-equal s ">>")
             (string-equal s ">>>")
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

(defconst holscript-symbolicthen-regexp "\\(?:>>\\|\\\\\\\\\\|>-\\|>|\\)")
(defconst holscript-textthen-regexp "\\(?:\\<\\(THEN\\([1L]?\\)\\)\\>\\)")
(defconst holscript-thenish-regexp
  (concat "\\(?:" holscript-symbolicthen-regexp "\\|"
          holscript-textthen-regexp "\\)"))
(defconst holscript-doublethen-error-regexp
  (concat holscript-thenish-regexp "[[:space:]]+" holscript-thenish-regexp))
(defun holscript-syntax-convert (n) (if (and n (equal (car n) 9)) '(1) n))
(defun holscript-bad-error-delims (p1 p2)
  (let ((s0 (holscript-syntax-convert (syntax-after (1- p1))))
        (s1 (holscript-syntax-convert (syntax-after p1)))
        (s2 (holscript-syntax-convert (syntax-after (1- p2))))
        (s3 (holscript-syntax-convert (syntax-after p2))))
    (or (equal s0 s1) (equal s2 s3))))

(defconst holscript-quoteddeclaration-begin
  (concat
   "^\\(Theorem\\|Triviality\\|Definition\\|Inductive\\|CoInductive\\)"
   "[[:space:]]+\\([A-Za-z0-9'_]+\\)[[:space:]]*" ; name
   "\\(\\[[A-Za-z0-9'_,]+\\]\\)?[[:space:]]*:"; optional annotations
   "\\|^Datatype[[:space:]]*:" ; or datatype (which has no following guff on same line)
   "\\|(Quote[[:space:]]*\\([A-Za-z0-9'_]+[[:space:]]*=\\)?"
   "[[:space:]]*[A-Za-z0-9'_.]*[[:space:]]*:)"
   )
  "Regular expression marking the beginning of the special syntax that marks
a store_thm equivalent.")

(defvar hol-quoted-block-opener-keywords
  '("Theorem" "Triviality" "Definition" "Inductive" "CoInductive" "Datatype")
  "Column-0 keywords that open a HOL block requiring a matching closer
from `hol-quoted-block-closer-keywords'.")

(defvar hol-quoted-block-closer-keywords
  '("End" "Proof" "Termination")
  "Column-0 keywords that close a HOL block opened by one of
`hol-quoted-block-opener-keywords'.  `Proof' closes Theorem/Triviality;
`Termination'/`End' close Definition; `End' closes
Inductive/CoInductive/Datatype.")

(defconst holscript-quoteddeclaration-end
  (regexp-opt hol-quoted-block-closer-keywords))

(defconst holscript-quotedmaterial-delimiter-fullregexp
  (concat holscript-quoteddeclaration-begin "\\|"
          holscript-quoteddeclaration-end "\\|[“”‘’]"))

(defcustom holscript-quoted-search-max-distance 20000
  "Maximum distance (in characters) that `holscript-in-quotedmaterialp'
will scan backward looking for a quoted-block opener.  Capping the
scan keeps the SMIE tokeniser and font-lock matchers responsive when
the buffer has an unterminated block above point.  A quoted block
whose opener exceeds the cap will not be detected as containing
point."
  :type 'integer
  :group 'holscript)

(defun holscript-in-quotedmaterialp (p &optional limit)
  "Return non-nil if buffer position P lies inside a HOL quoted-material
block.  Searches backward from P for a delimiter; the search is bounded
to LIMIT (a buffer position) when supplied, otherwise to
`holscript-quoted-search-max-distance' characters back from P."
  (save-match-data
    (save-mark-and-excursion
      (goto-char p)
      (let* ((limit (or limit
                        (max (point-min)
                             (- p holscript-quoted-search-max-distance))))
             (beginmatch
              (re-search-backward
               holscript-quotedmaterial-delimiter-fullregexp limit t))
             (ppss (syntax-ppss)))
        (while (and beginmatch (or (nth 3 ppss) (nth 4 ppss)))
          (setq beginmatch (re-search-backward
                            holscript-quotedmaterial-delimiter-fullregexp
                            limit t))
          (setq ppss (syntax-ppss)))
        (and beginmatch
             (or (and (looking-at holscript-quoteddeclaration-begin)
                      (>= p (match-end 0)))
                 (looking-at "[“‘]")))))))

(defun holscript-find-syntax-error (limit)
  (let ((beginmatch
         (re-search-forward holscript-doublethen-error-regexp limit t))
        (ppss (syntax-ppss)))
    (while (and beginmatch
                (or (nth 3 ppss) (nth 4 ppss)
                    (holscript-bad-error-delims (match-beginning 0)
                                                (match-end 0))
                    (holscript-in-quotedmaterialp (point))))
      (setq beginmatch
            (re-search-forward holscript-doublethen-error-regexp limit t))
      (setq ppss (syntax-ppss)))
    (if (not beginmatch) nil t)))

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
   (insert "Datatype:\n  TREE = LEAF ('a -> num) | BRANCH TREE TREE\nEnd\n"))

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
      (insert so)))))

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

;; Replace common unicode chars with ascii version; or vice versa.
;; Leading symbols explain how replacements need to be done.
;; - removeonly: apply this transformation only when removing unicode
;; - both: apply this transformation unilaterally in both directions
;; - spaceit: when moving from Unicode to ASCII, ensure the replacement has
;;   spaces around the replacement text (to avoid symbol merges); when moving
;;   from ASCII to Unicode, make sure the text is not within another symbol
;;   (you don't want TC_SUBSET, a theorem name, turning into TC_⊆)
;; - withspaces-for-unicode: unilaterally for Unicode->ASCII; avoiding in-
;;   symbol matches for the reverse direction
;;
;; In all cases, replacements never happen within string literals
(setq hol-unicode-replacements '(
  (removeonly "¬" "~")
  (removeonly "−" "-")
  (both "∧" "/\\")
  (both "∨" "\\/")
  (both "⇒" "==>")
  (both "⇔" "<=>")
  (both "⇎" "<=/=>")
  (both "≠" "<>")
  (both "∃" "?")
  (both "∀" "!")
  (both "⁺" "^+")
  (both "꙳" "^*")
  (both "⁼" "^=")
  (spaceit "∈" "IN")
  (spaceit "∉" "NOTIN")
  (spaceit "𝕌ᵣ" "RUNIV")
  (spaceit "𝕌" "univ")
  (spaceit "⊆ᵣ" "RSUBSET")
  (spaceit "⊆" "SUBSET")
  (spaceit "∪ᵣ" "RUNION")
  (spaceit "∪" "UNION")
  (spaceit "∩ᵣ" "RINTER")
  (spaceit "∩" "INTER")
  (spaceit "∅ᵣ" "EMPTY_REL")
  (spaceit "∅" "{}")
  (spaceit "≤₊" "<=+")
  (spaceit ">₊" ">+")
  (spaceit "<₊" "<+")
  (spaceit "≥₊" ">=+")
  (spaceit "≤" "<=")
  (spaceit "≥" ">=")
  (spaceit "⊕" "??")
  (spaceit "‖" "||")
  (spaceit "≪" "<<")
  (spaceit "≫" ">>")
  (spaceit "⋙" ">>>")
  (spaceit "⇄" "#>>")
  (spaceit "⇆" "#<<")
  (withspaces-for-unicode "α" "'a")
  (withspaces-for-unicode "β" "'b")
  (withspaces-for-unicode "γ" "'c")
  (withspaces-for-unicode "δ" "'d")
  (withspaces-for-unicode "ε" "'e")
  (withspaces-for-unicode "ζ" "'f")
  (withspaces-for-unicode "η" "'g")
  (withspaces-for-unicode "θ" "'h")
  (withspaces-for-unicode "ι" "'i")
  (withspaces-for-unicode "κ" "'j")
  (withspaces-for-unicode "μ" "'l")
  (withspaces-for-unicode "ν" "'m")
  (withspaces-for-unicode "ξ" "'n")
  (withspaces-for-unicode "ο" "'o")
  (withspaces-for-unicode "π" "'p")
  (withspaces-for-unicode "ρ" "'q")
  (withspaces-for-unicode "ς" "'r")
  (withspaces-for-unicode "σ" "'s")
  (withspaces-for-unicode "τ" "'t")
  (withspaces-for-unicode "υ" "'u")
  (withspaces-for-unicode "φ" "'v")
  (withspaces-for-unicode "χ" "'w")
  (withspaces-for-unicode "ψ" "'x")
  (withspaces-for-unicode "ω" "'y")
  (withspaces-for-unicode "∘ᵣ" "O")
  (withspaces-for-unicode "∘" "o")
))


(defun holscript-replace-regexp-in-buffer (src tgt &optional forcesafep)
   (save-excursion
      (goto-char (point-min))
      (let ((tgt-len (length tgt)))
        (while (re-search-forward src nil t)
          (let ((pp (syntax-ppss))
                (match-end (point))
                (match-start (match-beginning 0)))
            (if (not (nth 3 pp))
                (if forcesafep
                    (let* (

                       ;; 1. Get neighboring characters as integers
                       (prev-char (and (> match-start (point-min))
                                       (char-before match-start)))
                       (next-char (char-after match-end))

                       ;; 2. Get replacement string's boundary characters
                       (to-first-char (and (> tgt-len 0) (aref tgt 0)))
                       (to-last-char
                        (and (> tgt-len 0) (aref tgt (1- tgt-len))))

                       ;; 3. Extract syntax classes (returns a character code
                       ;;    like ?w or ?.)
                       (prev-syn (and prev-char (char-syntax prev-char)))
                       (next-syn (and next-char (char-syntax next-char)))
                       (first-syn (and to-first-char
                                       (char-syntax to-first-char)))
                       (last-syn  (and to-last-char (char-syntax to-last-char)))

                       ;; 4. Check for syntax conflicts
                       ;;    (exclude w/space class ?\s)
                       (prefix (if (and prev-syn first-syn
                                        (eq prev-syn first-syn)
                                        (not (eq prev-syn ?\s)))
                                   " " ""))
                       (suffix (if (and next-syn last-syn
                                        (eq next-syn last-syn)
                                        (not (eq next-syn ?\s)))
                                   " " "")))

                      ;; Perform the in-buffer replacement
                      (replace-match (concat prefix tgt suffix) t t))
                  (replace-match tgt t t))))))))

(defun hol-unicode-replacements (addunicodep)
  (save-excursion
    (save-restriction
      (if (use-region-p) (narrow-to-region (region-beginning) (region-end)))
      (let ((srci (if addunicodep 2 1))
            (tgti (if addunicodep 1 2))
            (case-fold-search (not addunicodep)))

        (dolist (elt hol-unicode-replacements)
          (let ((ty (nth 0 elt))
                (src (regexp-quote (nth srci elt)))
                (tgt (nth tgti elt)))
            (cond
             ((equal 'both ty)
              (holscript-replace-regexp-in-buffer src tgt))
             ((equal 'spaceit ty)
              (if addunicodep
                  (holscript-replace-regexp-in-buffer
                   (concat "\\_<" src "\\_>") tgt)
                (replace-regexp-in-buffer src tgt 't)))
             ((equal 'removeonly ty)
              (if (not addunicodep)
                  (holscript-replace-regexp-in-buffer src tgt)))
             ((equal 'withspaces-for-unicode ty)
              (if addunicodep
                  (holscript-replace-regexp-in-buffer
                   (concat "\\_<" src "\\_>") tgt 't)
                (holscript-replace-regexp-in-buffer src tgt)))
             ('t (message "No behaviour for symbol %s" ty)))))))))

(defun hol-add-unicode () (interactive) (hol-unicode-replacements 't))
(defun hol-remove-unicode () (interactive) (hol-unicode-replacements nil))

;; Editing-side syntactic knowledge of HOL declaration shapes.
;; holscript-mode is self-contained for editing; hol-mode
;; forward-references these for REPL-destined parsing.

(defvar hol-name-attrs-colon-re
  "[[:space:]]+[A-Za-z0-9'_]+\\(\\[[A-Za-z0-9_,]+\\]\\)?[[:space:]]*:")
(defvar hol-quoted-theorem-proof-re-begin
  (concat "\\(Theorem\\|Triviality\\)" hol-name-attrs-colon-re))
(defvar hol-quoted-definition-re-begin
  (concat "\\(Definition\\|\\(Co\\)?Inductive\\)" hol-name-attrs-colon-re))
(defvar hol-quoted-datatype-re-begin "\\(Datatype[[:space:]]*:\\)")
(defvar hol-quoted-Quote-re-begin
  (concat "\\(Quote[[:space:]]+\\([A-Za-z0-9_']+[[:space:]]*=[[:space:]]*\\)?"
          "[A-Za-z0-9_'.]+[[:space:]]*:\\)"))

(defvar hol-term-begin-re
  (concat
   (regexp-opt '("“" "‘")) "\\|"
   hol-quoted-theorem-proof-re-begin "\\|"
   hol-quoted-definition-re-begin "\\|"
   "Datatype[[:space:]]*:")
  "Regular expression matching the opening delimiter of a HOL block
or quoted-material region.  Used by `hol-find-quoted-material' and
by `hol-fl-term-bump-{backwards,forwards}'.")

(defcustom hol-fl-term-bump-max-distance 40000
  "Maximum distance (in characters) that `hol-fl-term-bump-backwards'
and `hol-fl-term-bump-forwards' will scan looking for an enclosing
HOL block delimiter.  Capping the scan keeps font-locking responsive
on large buffers whose nearest delimiter is far away (typically
because the user has just typed an unterminated block).  A multi-line
construct whose delimiter exceeds the cap will be fontified without
full context near the cap boundary."
  :type 'integer
  :group 'holscript)

(defvar hol-term-beginend-re
  (concat
   (regexp-opt
    (append hol-quoted-block-opener-keywords
            hol-quoted-block-closer-keywords)
    "^\\(")
   "\\|"
   (regexp-opt '("“" "‘" "”" "’")))
  "Regular expression for delimiters that begin or end a HOL block
or quoted-material region.  Used by `hol-fl-term-bump-backwards' and
`hol-fl-term-bump-forwards' to widen the font-lock region.")

(defvar hol-term-end-re
  (concat holscript-quoteddeclaration-end "\\|" (regexp-opt '("”" "’")))
  "Regular expression matching the closing delimiter of a HOL block
or quoted-material region.")

(defun hol-fl-term-bump-backwards (pos)
  (save-excursion
    (goto-char pos)
    (let* ((limit (max (point-min) (- pos hol-fl-term-bump-max-distance)))
           (match (re-search-backward hol-term-beginend-re limit t)))
      (if (not match) pos
        (if (looking-at hol-term-end-re) pos
          (if (looking-at hol-term-begin-re) (match-beginning 0) pos))))))

(defun hol-fl-term-bump-forwards (pos)
  (save-excursion
    (goto-char pos)
    (let* ((limit (min (point-max) (+ pos hol-fl-term-bump-max-distance)))
           (match (re-search-forward hol-term-beginend-re limit t)))
      (if (not match) pos
        (goto-char (match-beginning 0))
        (if (looking-at hol-term-begin-re) pos
          (if (looking-at hol-term-end-re) (match-end 0) pos))))))

(defun hol-term-matching-delim (start-delim)
  (cond
   ((equal start-delim "“") "”")
   ((equal start-delim "‘") "’")
   ((equal start-delim "Datatype:") "^End\\>")
   ((or (string-prefix-p "Theorem" start-delim)
        (string-prefix-p "Triviality" start-delim)) "^Proof\\>")
   ((or (string-prefix-p "Inductive" start-delim)
        (string-prefix-p "CoInductive" start-delim)) "^End\\>")
   ((string-prefix-p "Definition" start-delim)
    "^Termination\\>\\|^End\\>")))

(defun hol-find-quoted-material (limit)
  (let ((beginmatch (re-search-forward hol-term-begin-re limit t))
        (ppss (syntax-ppss)))
    (while (and beginmatch (or (nth 3 ppss) (nth 4 ppss)))
      (setq beginmatch (re-search-forward hol-term-begin-re limit t))
      (setq ppss (syntax-ppss)))
    (if (not beginmatch) nil
      (let* ((start-delim (match-string-no-properties 0))
             (begin-marker
              (if (= (length start-delim) 1)
                  (set-marker (make-marker) (1- (point)))
                (point-marker)))
             (endre (hol-term-matching-delim start-delim))
             (endmatch (if endre (re-search-forward endre limit t)
                         (message (format "No end-delim for %s" start-delim))
                         nil)))
        (if (not endmatch) nil
          (if (= (length start-delim) 1) nil (goto-char (match-beginning 0)))
          (set-match-data (list begin-marker (point-marker)))
          t)))))

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

(defvar hol-proof-beginend-re
  (regexp-opt (cons "QED" hol-quoted-block-closer-keywords) "^\\(")
  "Regular expression matching column-0 keywords that begin or end a
HOL proof or definition body.  Used by `hol-movement-in-proof-p'.")

(defun hol-movement-in-proof-p (pos)
  (save-excursion
    (goto-char pos)
    (let* ((pp (syntax-ppss))
           (limit (max (point-min)
                       (- pos holscript-quoted-search-max-distance))))
      (and (not (nth 3 pp)) (not (nth 4 pp))
           (let ((nextre (re-search-backward hol-proof-beginend-re limit t)))
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
  (unless (boundp 'hol-executable)
    (user-error
     "holscript-fix-quotations needs `hol-executable' (set by hol-mode)"))
  (shell-command-on-region start end
                           (concat (file-name-directory hol-executable)
                                   "unquote --quotefix")
                           nil
                           t))

(defun holscript--blink-without-smie (orig &rest args)
  "Around `blink-matching-open' in holscript-mode buffers: bind
`forward-sexp-function' to nil so blink uses the raw C-level paren
scanner instead of the SMIE token walker installed by `smie-setup'.
Blink-matching only needs to match `(' to `)', not navigate HOL
block structure; SMIE-driven backward-sexp across a large buffer
with an unmatched paren is hundreds of times slower."
  (if (derived-mode-p 'holscript-mode)
      (let ((forward-sexp-function nil)) (apply orig args))
    (apply orig args)))
(advice-add 'blink-matching-open :around #'holscript--blink-without-smie)

(defcustom holscript-show-paren-max-distance 10000
  "Maximum distance (in characters) that show-paren-mode's
SMIE-driven block-pair matcher will search forward or backward from
point.  Capping it keeps the show-paren idle timer responsive when
the buffer has an unmatched paren; SMIE block pairs (`Theorem'
/ `QED', `let' / `end', etc.) more than this many characters from
point will not be highlighted, but `(' / `)' / `[' / `]' matching
continues to work via the underlying `show-paren--default'."
  :type 'integer
  :group 'holscript)

(defun holscript--show-paren-bounded (orig &rest args)
  "Around the local `show-paren-data-function' chain in
holscript-mode buffers: narrow to a window of width
`holscript-show-paren-max-distance' around point before running
the rest of the chain (which includes `smie--matching-block-data'
installed by `smie-setup').  This bounds how far
`smie-backward-sexp' walks looking for a structural match."
  (save-restriction
    (narrow-to-region
     (max (point-min) (- (point) holscript-show-paren-max-distance))
     (min (point-max) (+ (point) holscript-show-paren-max-distance)))
    (apply orig args)))

(defun holscript-mode-variables ()
  (set-syntax-table holscript-mode-syntax-table)
  (setq local-abbrev-table holscript-mode-abbrev-table)
  (smie-setup holscript-smie-grammar #'holscript-smie-rules
              :backward-token #'holscript-smie-backward-token
              :forward-token #'holscript-smie-forward-token)
  ;; Bound the SMIE-driven `show-paren-data-function' advice that
  ;; `smie-setup' installs.  Without a bound, on a large *Script.sml
  ;; with an unmatched paren the advice calls `smie-backward-sexp'
  ;; which walks the entire buffer's SMIE token stream looking for a
  ;; structural match — ~500 ms per call, blocking the show-paren
  ;; idle timer and any keystroke queued behind it.  Narrowing to a
  ;; window around point keeps SMIE block-pair highlighting
  ;; (`Theorem'/`QED', `let'/`end') for pairs within the window and
  ;; fails fast when there is no match.
  (add-function :around (local 'show-paren-data-function)
                #'holscript--show-paren-bounded)
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
      (sml-expr (sml-expr "SML|>" sml-expr))
      (decls (decls ";" decls) (decl))
      (decl ("^Theorem" theorem-contents "^QED")
            ("^Triviality" theorem-contents "^QED")
            ("^Resume" resume-contents "^QED")
            ("^Theorem=" sml-expr)
            ("^Finalise" sml-expr)
            ("^Triviality=" id)
            ("^Definition" definition-contents "^End")
            ("^Quote" id-quoted "^End")
            ("^Inductive" id-quoted "^End")
            ("^CoInductive" id-quoted "^End")
            ("^Overload" id)
            ("^Type" id)
            ("^Datatype:" quotedmaterial "^End")
            ("val" id)
            ("fun" id)
            ("open" id)
            ("datatype" id)
            ("structure" id))
      (resume-contents (id "SML:" tactic))
      (theorem-contents (id-quoted "^Proof" tactic)
                        (id-quoted "^Proof" "PF[" attributes "PF]" tactic))
      (attributes (attribute) (attributes "," attributes))
      (definition-contents (id-quoted "^Termination" tactic) (id-quoted))
      (id-quoted (id "SML:" quotedmaterial))
      (quotedmaterial
        ("QFIER." quotedmaterial "ENDQ." quotedmaterial)
        (quotedmaterial "+" quotedmaterial)
        (quotedmaterial "-" quotedmaterial)
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
        (quotedmaterial "++" quotedmaterial)
        (quotedmaterial "*" quotedmaterial)
        (quotedmaterial ":=" quotedmaterial)
        (quotedmaterial "<-" quotedmaterial)
        (quotedmaterial "|" quotedmaterial)
        (quotedmaterial "=>" quotedmaterial)
        (quotedmaterial ":" quotedmaterial)
        ("(" quotedmaterial ")")
        ("[defnlabel]" quotedmaterial)
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
              (tactic ">~" tactic)
              (tactic "THEN_LT" tactic)
              (tactic "THEN" tactic)
              (tactic "THEN1" tactic)
              (tactic "THENL" tactic)
              (quotation "by" tactic)
              (quotation "suffices_by" tactic)
              ("[" tactics "]"))
      (tactics (tactic) (tactics "," tactics)))
    '((assoc ",")) '((assoc ";")) '((assoc "SML|>"))
    '((assoc "^Proof")
      (left ">>" "\\\\" ">-"  ">|" "THEN" "THEN1" "THENL" "THEN_LT" ">~")
      (assoc "by" "suffices_by"))
    '((assoc "ENDQ." "QFIER." "in" "of") ; HOL syntax
      (assoc "|")
      (assoc "=>")
      (assoc "else")
      (assoc "<=>" "⇔" "<-")
      (assoc "==>" "⇒") (assoc "\\/" "∨") (assoc "/\\" "∧")
      (assoc "[defnlabel]")
      (assoc "=" "<" "≤" "<=") (assoc ":=") (assoc "++" "+" "-") (assoc "*")
      (assoc ":")))))

(defvar holscript-quotedmaterial-delimiter-regexp
  (regexp-opt (list "“" "”" "‘" "’" holscript-quoteddeclaration-begin)))

(defvar holscript-boolean-quantifiers '("∀" "∃" "∃!"))

(defvar holscript-quantifier-regexp
  (concat (regexp-opt holscript-boolean-quantifiers) "\\|"
          (regexp-opt '("some" "LEAST") 'symbols))
  "List of strings that can begin \"quantifier blocks\".")

(defvar holscript-lambda-regexp "[λ\\!?@]\\|?!"
  "Regular expression for quantifiers that are (treated as) single punctuation
class characters.")





(defun holscript-can-find-earlier-quantifier (pp)
  (let* ((pstk (nth 9 pp))
         (raw-limit (car (last pstk)))
         ;; Cap the scan distance even when there is no enclosing paren
         ;; (or when the outermost paren is far away because of an
         ;; unbalanced `(' at the top of the buffer).  HOL declarations
         ;; like `Definition foo: ... End' are not bracketed by
         ;; paren-syntax characters, so the paren stack can legitimately
         ;; be empty inside a HOL term: we must keep searching past
         ;; raw-limit, just not to point-min.
         (cap (max (point-min)
                   (- (point) holscript-quoted-search-max-distance)))
         (limit (if raw-limit (max raw-limit cap) cap))
         (case-fold-search nil))
    (save-mark-and-excursion
      (catch 'found-one
        (while (re-search-backward
                (concat "\\(" holscript-quoteddeclaration-begin "\\)" "\\|"
                        "\\(" holscript-quoteddeclaration-end "\\)" "\\|"
                        holscript-quotedmaterial-delimiter-regexp "\\|"
                        holscript-quantifier-regexp "\\|"
                        holscript-lambda-regexp "\\|\\.")
                limit
                t)
          (let ((pp1 (syntax-ppss))
                (sa (holscript-syntax-convert (syntax-after (point))))
                (sb (holscript-syntax-convert (syntax-after (1- (point))))))
            (if (or (nth 3 pp1) (nth 4 pp1))
                (goto-char (nth 8 pp1))
              (if (and sb (equal sa sb))
                  (progn (forward-char -1)
                         (if (or (looking-at "∃!") (looking-at "?!"))
                             (throw 'found-one (point))))
                (if (equal (car (last (nth 9 pp1))) raw-limit)
                    (if (or (looking-at holscript-quantifier-regexp)
                            (looking-at holscript-lambda-regexp)
                            (looking-at "\\\\"))
                        (throw 'found-one (point))
                      (throw 'found-one nil)))))))))))

(defconst holscript-column0-keywords-regexp
  (regexp-opt '("Definition" "Datatype" "Theorem" "Triviality" "Type"
                "Proof" "Quote" "Theory" "Ancestors" "Libs"
                "Termination" "End" "QED" "Inductive" "CoInductive"
                "Overload" "Resume" "Finalise")))
(defconst holscript-column0-declbegin-keyword
  (regexp-opt '("Definition" "Datatype" "Theorem" "Triviality" "Resume" "Quote"
                "Type" "Inductive" "CoInductive" "Overload" "Finalise")))

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

(defun holscript-after-proof-keyword ()
  (save-mark-and-excursion
    (skip-chars-backward " \t\n")
    (looking-back "\\<Proof" (- (point) 6))))

(defun holscript-smie-forward-token ()
  (let ((p0 (point))
        (case-fold-search nil))
    (forward-comment (point-max))
    (if (and (not (= p0 (point)))
             (or (looking-at
                  (concat holscript-column0-declbegin-keyword
                          "\\([[:space:]]\\|[[:space:]]*:\\)"))
                 (looking-at (concat "^" holscript-sml-declaration-keyword))))
        ";"
      (let ((pp (syntax-ppss))
            (sclass-number (syntax-class (syntax-after (point)))))
        (cond
         ((and (looking-at (concat "\\(" holscript-column0-keywords-regexp
                                   "\\)" "\\([[:space:]]\\|[[:]\\)"))
               (save-excursion (skip-chars-backward " \t") (bolp)))
          (goto-char (match-end 1))
          (let ((ms (match-string-no-properties 1)))
            (if (or (string= ms "Theorem")
                    (string= ms "Triviality")
                    (string= ms "Resume"))
                (let ((eolpoint (save-excursion (end-of-line) (point))))
                  (save-excursion
                    (if (re-search-forward ":" eolpoint t) (concat "^" ms)
                      (concat "^" ms "="))))
              (if (and (string= ms "Datatype") (looking-at "[[:space:]]*:"))
                  (progn (goto-char (match-end 0)) (concat "^" ms ":"))
                (concat "^" ms)))))
         ((looking-at holscript-quotedmaterial-delimiter-regexp)
          (goto-char (match-end 0))
          (match-string-no-properties 0))
         ((and (looking-at holscript-definitionlabel-re)
               (save-excursion (skip-chars-backward " \t") (bolp)))
          (goto-char (match-end 0))
          "[defnlabel]")
         ((looking-at ":\\([^[:punct:]]\\|[(]\\)")
          (let ((p (point)))
            (goto-char (1- (match-end 0)))
            (if (holscript-in-quotedmaterialp p) ":" "SML:")))
         ((looking-at "\\\\/") (goto-char (match-end 0)) "\\/")
         ((looking-at "/\\\\") (goto-char (match-end 0)) "/\\")
         ((looking-at "\\\\\\\\") (goto-char (match-end 0)) "\\\\")
         ((looking-at "\\.")
          (if (or (nth 3 pp) (nth 4 pp))
              (progn (forward-char 1) ".")
            (let ((tok
                   (if (holscript-can-find-earlier-quantifier pp) "ENDQ."
                     ".")))
              (forward-char 1) tok)))
         ((looking-at holscript-quantifier-regexp)
          (goto-char (match-end 0)) "QFIER.")
         ((looking-at (concat "\\(?:" holscript-lambda-regexp "\\)\\S."))
          (if (equal 1 (syntax-class (syntax-after (1- (point)))))
              (buffer-substring-no-properties
               (point)
               (progn (skip-syntax-forward ".") (point)))
            (forward-char 1) "QFIER."))
         ((looking-at (regexp-quote "|>"))
          (goto-char (match-end 0))
          (if (holscript-in-quotedmaterialp (point)) "|>" "SML|>"))
         ((equal 4 sclass-number)
          ;; looking at an open paren (could be LPAREN, LBRACK, LBRACE
          (let ((c (char-after)))
            (if
                (and (equal c ?\[) (holscript-after-proof-keyword))
                (progn (forward-char 1) "PF[")
              (forward-char 1) (string c))))
         ((equal 5 sclass-number)
          ;; close paren symbol
          (let ((c (char-after)))
            (forward-char)
            (if (equal c ?\])
                (save-mark-and-excursion
                  (holscript-maybe-skip-attr-list-backward)
                  (if (and (equal (char-after) ?\[)
                           (holscript-after-proof-keyword))
                      "PF]"
                    (string c)))
              (string c))))
         ((equal 1 sclass-number)
          ;; looking at "punctuation", meaning that it's what HOL could consider
          ;; "symbolic"
          (let* ((symstr (buffer-substring-no-properties
                         (point)
                         (progn (skip-syntax-forward ".") (point))))
                 (ldel1 (cl-search "<|" symstr))
                 (rdel1 (cl-search "|>" symstr))
                 (del1 (or (and ldel1 rdel1 (min ldel1 rdel1)) ldel1 rdel1)))
            (cond
             (del1
              (if (= del1 0)
                  (progn
                    (forward-char (- 2 (length symstr)))
                    (substring symstr 0 2))
                (forward-char (- del1 (length symstr)))
                (substring symstr 0 del1)))
             ((and (string= symstr "=")
                   (save-mark-and-excursion
                    (beginning-of-line)
                    (looking-at "Quote")))
              "MQ=")
             (t symstr))))
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
              (skip-syntax-forward "w_")
              (if (looking-at "\\$")
                  (progn (forward-char 1)
                         (holscript-simple-token-forward)))
              (buffer-substring-no-properties p (point)))))))))

(defun holscript-maybe-skip-attr-list-backward ()
  (let ((c (char-before)))
    (cond
     ((null c) t)
     ((char-equal c ?\])
      (forward-char -1)
      (skip-chars-backward "A-Za-z0-9_'.,= \t\n")
      (and (eq (char-before) ?\[) (progn (forward-char -1) t)))
     (t t))))

(defun holscript-smie-backward-token ()
  (let ((case-fold-search nil))
    (if (or (and (looking-at
                  (concat holscript-column0-declbegin-keyword
                          "\\([[:space:]]\\|[[:space:]]*:\\)"))
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
      (let ((sclass-number (syntax-class (syntax-after (1- (point))))))
      (cond
       (; am I just after a keyword?
        (and (save-excursion
               (backward-word)
               (or
                (looking-at holscript-column0-keywords-regexp)
                (looking-at "^\\(Datatype\\)[[:space:]]*:")))
             (let ((syn (syntax-after (point))))
               ; next char is whitespace or colon or left square bracket
               (or (null syn) (= 0 (car syn)) (char-equal (char-after) ?:)
                   (char-equal (char-after) ?\[)))
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
            (if (looking-at "Datatype[[:space:]]*:") "^Datatype:"
              (concat "^" ms)))))
       (; am I just after a quotation mark
        (looking-back holscript-quotedmaterial-delimiter-regexp (- (point) 1) t)
        (goto-char (match-beginning 0))
        (match-string-no-properties 0))
       (; am I after a definition-label
        (and (equal (char-before) ?\])
             (let ((p (point)))
               (forward-char -1)
               (skip-chars-backward " \t")
               (if (equal (char-before) ?:)
                   (progn (forward-char -1)
                          (skip-chars-backward " \t")
                          (if (holscript-maybe-skip-attr-list-backward)
                              (progn
                                (skip-chars-backward "A-Za-z0-9_'")
                                (if (equal (char-before) ?~) (forward-char -1))
                                (skip-chars-backward " \t")
                                (equal (char-before) ?\[))
                            (goto-char p) nil))
                 (goto-char p) nil)))
        (forward-char -1) "[defnlabel]")
       (; am I just after a quantifier
        (looking-back holscript-quantifier-regexp (- (point) 10) t)
        (goto-char (match-beginning 0))
        (let ((c (char-before)))
          (if (and c (char-equal c ?$))
              (progn (backward-char) (concat "$" (match-string-no-properties 0)))
            "QFIER.")))
       ((looking-back "\\\\\\\\" (- (point) 3))
        (goto-char (match-beginning 0)) "\\\\")
       (; am I just after either a backslash or Greek lambda?
        (looking-back (concat "\\([^$[:punct:]]\\|[~()“‘]\\)"
                              holscript-lambda-regexp)
                      (- (point) 3) nil)
        (if (equal 1 (syntax-class (syntax-after (point))))
            (buffer-substring-no-properties
             (point)
             (progn (skip-syntax-backward ".") (point)))
          (backward-char) "QFIER."))
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
       ((looking-back "\\([^[:punct:]]\\|[])']\\):" (- (point) 3))
        (goto-char (1+ (match-beginning 0)))
        (if (holscript-in-quotedmaterialp (point)) ":" "SML:"))
       ((looking-back (regexp-quote "|>") (- (point) 3))
        (goto-char (match-beginning 0))
        (if (holscript-in-quotedmaterialp (point)) "|>" "SML|>"))
       ((equal 4 sclass-number)
        ;; sitting after a left-paren class thing
        (backward-char)
        (let ((c (char-after)))
          (if (and (equal ?\[ c) (holscript-after-proof-keyword))
              "PF["
            (string c))))
       ((equal 5 sclass-number)
        (let ((c (char-before)))
          (backward-char)
          (if (equal c ?\])
              (save-mark-and-excursion
                (forward-char)
                (holscript-maybe-skip-attr-list-backward)
                (if (and (equal ?\[ (char-after))
                         (holscript-after-proof-keyword))
                    "PF]" (string c)))
            (string c))))
       (; am I sitting after "punctuation"
        (equal 1 sclass-number)
        (let* ((symstr (buffer-substring-no-properties
                        (point)
                        (progn (skip-syntax-backward ".") (point))))
               (ldel (and (string-match ".*\\(<|\\)" symstr)
                          (match-end 1)))
               (rdel (and (string-match ".*\\(|>\\)" symstr)
                          (match-end 1)))
               (del (or (and ldel rdel (max ldel rdel)) ldel rdel))
               (sz (length symstr)))
          (cond
           (del
            (if (= del sz) (progn (forward-char (- sz 2))
                                  (substring symstr -2 nil))
              (forward-char del)
              (substring symstr del nil)))
           ((and (string= symstr "=")
                   (save-mark-and-excursion
                    (beginning-of-line)
                    (looking-at "Quote")))
            "MQ=")
           (t symstr))))
       (t (buffer-substring-no-properties
           (point)
           (progn (skip-syntax-backward "w_")
                  (point)))))))))

(defvar holscript-indent-level 0 "Default indentation level")
(defcustom holscript-debugging-messages-p nil
  "Whether or not to emit debugging messages"
  :type 'boolean)
(defun holscript-message (s &rest rest)
  (if holscript-debugging-messages-p (apply 'message s rest)))
(defun holscript-smie-rules (kind token)
  (holscript-message "in smie rules, %d looking at (%s,>%s<)"
                     (point) kind token)
  (pcase (cons kind token)
    (`(:elem  . basic) (holscript-message "In elem rule") 0)
    (`(:list-intro . "SML:")
     (holscript-message "In list-intro :")
     holscript-indent-level)
    (`(:list-intro . "‘") 1)
    (`(:list-intro . "“") 1)
    (`(:list-intro . "")
     (holscript-message "In (:list-intro \"\"))") holscript-indent-level)
    (`(:after . "SML:") 2)
    (`(:before . "SML|>")
     (holscript-message "|> Current column = %d" (current-column))
     (save-mark-and-excursion
       (forward-char 2)
       (backward-sexp 1)
       (if (looking-back (concat (regexp-quote "|>") "[[:space:]]*")
                         (- (point) 10))
           (progn
             (goto-char (match-beginning 0))
             (cons 'column (current-column)))
         (cons 'column (+ (current-column) 2)))))
    (`(:before . "^CoInductive") '(column . 0))
    (`(:before . "^Definition") '(column . 0))
    (`(:before . "^Inductive") '(column . 0))
    (`(:before . "^Proof") '(column . 0))
    (`(:before . "^QED") '(column . 0))
    (`(:before . "^Termination") '(column . 0))
    (`(:before . "^Theorem") '(column . 0))
    (`(:before . "^Quote") '(column . 0))
    (`(:before . "^Theorem=") '(column . 0))
    (`(:before . "[defnlabel]") '(column . 0))
    (`(:after . "[defnlabel]") 2)
    (`(:after . "^Proof") 2)
    (`(:after . "PF]") 2)
    (`(:after . "^Termination") 2)
    (`(:after . "^Datatype:") 2)
    (`(:after . "^Quote:") 2)
    (`(:before . "val") 0)
    (`(:before . "fun") 0)
    (`(:before . "open") 0)
    (`(:before . "ENDQ.") 0)
    (`(:after . "ENDQ.") 2)
    (`(:after . ";") 0)
    (`(:before . "let") (if (smie-rule-bolp) nil 0))
    (`(:after . "let")
     (if (smie-rule-hanging-p)
         (progn (holscript-message "let-hanging")
                (cons 'column (+ (current-column) 2)))
       (holscript-message "Not let-hanging") 2))
    (`(:after . "in") 2)
    (`(:before . "in")
     (if (smie-rule-parent-p "let")
         (progn (holscript-message "in: let a parent")
                (save-excursion
                  (backward-up-list)
                  (cons 'column (current-column))))
       (smie-rule-parent)))
    (`(:after . "then") 2)
    (`(:after . "else") 2)
    (`(:after . "of") (if (smie-rule-next-p "|") 0 2))
    (`(:before . "|") (if (smie-rule-parent-p "of") 0))
    (`(:before ."if")
     (and (not (smie-rule-bolp))
          (smie-rule-prev-p "else")
          (smie-rule-parent)))
    (`(:before . "SML:") holscript-indent-level)
    (`(:after . "=>") 2)
    (`(:after . "do") 2)
    ; (`(:before . "==>") 2)
    ; (`(:before . "⇒") 2)
    (`(:before . ,(or `"[" `"(" `"{"))
     (if (smie-rule-hanging-p) (smie-rule-parent 2)))
    (`(:before . "by")  (cond ((smie-rule-parent-p "^Proof") 4)
                              ((smie-rule-parent-p "(" "[") 3)
                              (t 2)))
    (`(:before . "suffices_by") (cond ((smie-rule-parent-p "^Proof") 4)
                                      ((smie-rule-parent-p "(" "[") 3)
                                      (t 2)))
    (`(:close-all . _) t)
    (`(:after . "[") 2)
    (`(:before . "PF[") 0)
    (`(:after . "PF[") 2)
    (`(:after . "<|") 2)
    (`(:after . ">-") 1)
    (`(:after . "‘") 1)
    (`(:after . "“") 1)
    (`(:after . "THEN1") 1)
    (`(:after . "⇔") 2)
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

(defface holscript-syntax-error-face
  '((((class color)) :foreground "red" :background "yellow"
     :weight bold :box t))
  "The face for highlighting guaranteed syntax errors."
  :group 'holscript-faces)

(defface holscript-definition-label-face
  '((((class color))
     :foreground "PaleVioletRed4"
     :box (:line-width 1 :color "PaleVioletRed4" :style released-button)
     :slant normal :weight light))
  "The face for highlighting definition labels in HOL material."
  :group 'holscript-faces)

;; The sibling holscript-ts-mode.el lives in a sub-directory so that
;; loading it is optional (it depends on Emacs 29+ `treesit' and a
;; compiled `holscript' parser library).  Make it visible to
;; `require' regardless of how the user wired their load-path.
(eval-and-compile
  (when load-file-name
    (let ((ts-dir (expand-file-name
                   "tree-sitter"
                   (file-name-directory load-file-name))))
      (when (file-directory-p ts-dir)
        (add-to-list 'load-path ts-dir)))))

(defun holscript-pick-mode ()
  "Choose between `holscript-ts-mode' and `holscript-mode' for the
current buffer.  Prefers `holscript-ts-mode' when its tree-sitter
parser is available; otherwise falls back to the SMIE-based
`holscript-mode'.  Bound to *Script.sml files via `auto-mode-alist'."
  (if (and (require 'treesit nil 'noerror)
           (treesit-ready-p 'holscript 'quiet)
           (require 'holscript-ts-mode nil 'noerror))
      (holscript-ts-mode)
    (holscript-mode)))

(setq auto-mode-alist (cons '("Script\\.sml" . holscript-pick-mode)
                            auto-mode-alist))

(if (boundp 'yas-snippet-dirs)
    (progn
      (setq yas-snippet-dirs
            (append
             yas-snippet-dirs
             (list (concat
                    hol-dir
                    "tools/editor-modes/emacs/yasnippets"))))
      (yas-reload-all)
      (add-hook 'holscript-mode-hook #'yas-minor-mode)
      (add-hook 'holscript-mode-hook
                (lambda () (setq yas-also-auto-indent-first-line t)))))
