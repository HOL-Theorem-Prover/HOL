;;; -*- emacs-lisp -*-
;;; to use this mode, you will need to do something along the lines of
;;; the following and have it in your .emacs file:
;;;    (setq hol98-executable "<fullpath to HOL98 executable>")
;;;    (load "<fullpath to this file>")

;;; The fullpath to this file can be just the name of the file, if
;;; your elisp variable load-path includes the directory where it
;;; lives.

(define-prefix-command 'hol-map)
(make-variable-buffer-local 'hol-buffer-name)
(make-variable-buffer-local 'hol-buffer-ready)
(set-default 'hol-buffer-ready nil)
(set-default 'hol-buffer-name nil)

(defvar hol98-executable "/local/scratch/kxs/hol98.3/bin/hol.enquote"
  "*Path-name for the HOL98 executable.")

(put 'hol-term 'end-op
     (function (lambda () (skip-chars-forward "^`"))))
(put 'hol-term 'beginning-op
     (function (lambda () (skip-chars-backward "^`"))))
(defun hol-term-at-point () (thing-at-point 'hol-term))

;;; makes buffer hol aware.  Currently this consists of no more than
;;; altering the syntax table if its major is sml-mode.
(defun make-buffer-hol-ready ()
  (if (eq major-mode 'sml-mode)
      (progn
        (modify-syntax-entry ?` "$")
        (modify-syntax-entry ?\\ "\\"))))

(defun hol-buffer-ok (string)
  "Checks a string to see if it is the name of a good HOL buffer.
In reality this comes down to checking that a buffer-name has a live
process in it."
  (and string (get-buffer-process string)
       (eq 'run
           (process-status
            (get-buffer-process string)))))

(defun ensure-hol-buffer-ok ()
  "Ensures by prompting that a HOL buffer name is OK, and returns it."
  (if (hol-buffer-ok hol-buffer-name) hol-buffer-name
    (message
     (cond (hol-buffer-name (concat hol-buffer-name " not valid anymore."))
           (t "Please choose a HOL to attach this buffer to.")))
    (sleep-for 1)
    (setq hol-buffer-name (read-buffer "HOL buffer: " nil t))
    (while (not (hol-buffer-ok hol-buffer-name))
      (ding)
      (message "Not a valid HOL process")
      (sleep-for 1)
      (setq hol-buffer-name
            (read-buffer "HOL buffer: " nil t)))
    hol-buffer-name)
  (if (not hol-buffer-ready)
      (progn (make-buffer-hol-ready) (setq hol-buffer-ready t))))


(defun is-a-then (s)
  (and s (or (string-equal s "THEN") (string-equal s "THENL"))))

(defun next-hol-lexeme-terminates-tactic ()
  (skip-syntax-forward " ")
  (or (char-equal (following-char) ?,) (is-a-then (word-at-point))))

(defun previous-hol-lexeme-terminates-tactic ()
  (save-excursion
    (skip-syntax-backward " ")
    (or (char-equal (preceding-char) ?,)
        (and (condition-case nil
                 (progn (backward-char 1) t)
                 (error nil))
             (is-a-then (word-at-point))))))

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

(defun find-tactic-extent ()
  (interactive)
  (let* (;; first search forward
         (endpt
          (save-excursion
            (while (and (not (next-hol-lexeme-terminates-tactic))
                        (my-forward-sexp)) nil)
            (skip-syntax-backward " ")
            (point)))
         (startpt
          (save-excursion
            (while (and (not (previous-hol-lexeme-terminates-tactic))
                        (my-backward-sexp)) nil)
            (point))))
    (goto-char endpt)
    (push-mark startpt nil t)))


(defun copy-region-as-hol-tactic (start end arg)
  "Send selected region to HOL process as tactic."
  (interactive "r\nP")
  (let* ((region-string (buffer-substring start end))
         (e-string (concat "goalstackLib." (if arg "expandf" "e")))
         (tactic-string
          (format "%s (%s) handle e => Raise e" e-string region-string)))
    (send-string-to-hol tactic-string)))

(defun send-string-as-hol-goal (s)
  (let ((goal-string
         (format  "goalstackLib.g `%s`" s)))
    (send-string-to-hol goal-string)
    (send-string-to-hol "goalstackLib.set_backup 100;")))

(defun hol-do-goal (arg)
  "Send term around point to HOL process as goal.
If prefix ARG is true, or if in transient mark mode and region is active
then send region instead."
  (interactive "P")
  (if (or (and mark-active transient-mark-mode) arg)
      (send-string-as-hol-goal
       (buffer-substring (region-beginning) (region-end)))
    (send-string-as-hol-goal (hol-term-at-point))))


(defun copy-region-as-hol-definition (start end arg)
  "Send selected region to HOL process as definition/expression."
  (interactive "r\nP")
  (let* ((buffer-string (buffer-substring start end))
         (send-string (if arg
                         (concat "(" buffer-string ") handle e => Raise e")
                       buffer-string)))
    (send-string-to-hol send-string)))

(defun hol-name-top-theorem (string arg)
  "Name the top theorem of the goalstackLib."
  (interactive "sName for top theorem: \nP")
  (if (not (string= string ""))
      (send-string-to-hol (format "val %s = top_thm()" string)))
  (if arg (send-string-to-hol "drop()")))

(defun send-string-to-hol (string)
  "Send a string to HOL process."
  (interactive "sString to send to HOL process: ")
  (let ((buf (ensure-hol-buffer-ok)))
    (comint-send-string buf (concat string ";\n"))))

(defun hol-backup ()
  "Perform a HOL backup."
  (interactive)
  (send-string-to-hol "goalstackLib.b()"))

(defun hol-print ()
  "Print the current HOL goal."
  (interactive)
  (send-string-to-hol "goalstackLib.p()"))

(defun hol-interrupt ()
  "Perform a HOL interrupt."
  (interactive)
  (let ((buf (ensure-hol-buffer-ok)))
    (interrupt-process (get-buffer-process buf))))

(defun hol-recentre ()
  "Display the HOL window in such a way that it displays most text."
  (interactive)
  (ensure-hol-buffer-ok)
  (save-selected-window
    (select-window (get-buffer-window hol-buffer-name t))
    ;; (delete-other-windows)
    (raise-frame)
    (goto-char (point-max))
    (recenter -1)))

(defun hol-rotate (arg)
  "Rotate the goal stack N times.  Once by default."
  (interactive "p")
  (send-string-to-hol (format "goalstackLib.r %d" arg)))

(defun copy-region-as-wmizar-tactic (start end)
  "Send the region as a wmizar tactic (with pe).
(In other words the pe function must be defined and must expect a term
 frag list.)"
  (interactive "r")
  (let* ((region-string (buffer-substring start end))
         (tactic-string
          (format "goalstackLib.e (dpt `%s`) handle e => Raise e"
                  region-string)))
    (send-string-to-hol tactic-string)))

(defun hol-scroll-up (arg)
  "Scrolls the HOL window."
  (interactive "P")
  (ensure-hol-buffer-ok)
  (save-excursion
    (select-window (get-buffer-window hol-buffer-name t))
    (scroll-up arg)))

(defun hol-scroll-down (arg)
  "Scrolls the HOL window."
  (interactive "P")
  (ensure-hol-buffer-ok)
  (save-excursion
    (select-window (get-buffer-window hol-buffer-name t))
    (scroll-down arg)))

(defun hol-use-file (filename)
  "Gets HOL session to \"use\" a file."
  (interactive "fFile to use: ")
  (send-string-to-hol (concat "use \"" filename "\";")))

(defun hol-load-string (s)
  (send-string-to-hol
   (concat "(print  \"Loading " s "\\n\"; " "load \"" s "\");")))

(defun hol-load-file (arg)
  "Gets HOL session to \"load\" the file at point.
If there is no filename at point, then prompt for file.
If the region is active (in transient mark mode) then send region instead.
With prefix ARG prompt for a file-name to load.  "
  (interactive "P")
  (let* ((wap (word-at-point))
         (s (if (and mark-active transient-mark-mode)
                (buffer-substring (region-beginning) (region-end))
              (if (or (not wap) arg) (read-string "Library to load: ") wap))))
    (hol-load-string s)))

;** hol map keys and function definitions

(defun hol98 (niceness)
  "Runs a HOL98 session in a comint window.
With a numeric prefix argument, runs it niced to that level
or at level 10 with a bare prefix. "
  (interactive "P")
  (let* ((niceval (cond ((null niceness) 0)
                        ((listp niceness) 10)
                        (t (prefix-numeric-value niceness))))
         (holname (format "HOL98(n:%d)" niceval))
         (buf (cond ((> niceval 0)
                     (make-comint holname "nice" nil
                                  (format "-%d" niceval)
                                  hol98-executable))
                    (t (make-comint "HOL98" hol98-executable)))))
    (setq hol-buffer-name (buffer-name buf))
    (switch-to-buffer buf)
    (setq hol-buffer-name (buffer-name buf))
    (setq comint-scroll-show-maximum-output t)))

(defun run-program (filename niceness)
  "Runs a PROGRAM in a comint window, with a given (optional) NICENESS."
  (interactive "fProgram to run: \nP")
  (let* ((niceval (cond ((null niceness) 0)
                        ((listp niceness) 10)
                        (t (prefix-numeric-value niceness))))
         (progname (format "%s(n:%d)"
                          (file-name-nondirectory filename)
                          niceval))
         (buf (cond ((> niceval 0)
                     (make-comint progname "nice" nil
                                  (format "-%d" niceval)
                                  (expand-file-name filename)))
                   (t (make-comint progname
                                   (expand-file-name filename)
                                   nil)))))
    (switch-to-buffer buf)))

(defun hol-toggle-show-types ()
  "Toggles the globals show_types variable."
  (interactive)
  (message "Toggling show_types")
  (send-string-to-hol "Globals.show_types := not (!Globals.show_types)"))

(defun set-hol-executable (filename)
  "Sets the HOL executable variable to be equal to FILENAME."
  (interactive "fHOL executable: ")
  (setq hol98-executable filename))

(defun hol-restart-goal ()
  "Restarts the current goal."
  (interactive)
  (send-string-to-hol "goalstackLib.restart()"))

(defun hol-drop-goal ()
  "Drops the current goal."
  (interactive)
  (send-string-to-hol "goalstackLib.drop()"))

(define-key global-map "\M-h" 'hol-map)

(define-key hol-map "\C-c" 'hol-interrupt)
(define-key hol-map "\C-l" 'hol-recentre)
(define-key hol-map "\C-v" 'hol-scroll-up)
(define-key hol-map "\M-v" 'hol-scroll-down)
(define-key hol-map "b"    'hol-backup)
(define-key hol-map "d"    'hol-drop-goal)
(define-key hol-map "e"    'copy-region-as-hol-tactic)
(define-key hol-map "g"    'hol-do-goal)
(define-key hol-map "h"    'hol98)
(define-key hol-map "l"    'hol-load-file)
(define-key hol-map "m"    'copy-region-as-wmizar-tactic)
(define-key hol-map "n"    'hol-name-top-theorem)
(define-key hol-map "p"    'hol-print)
(define-key hol-map "\M-r" 'copy-region-as-hol-definition)
(define-key hol-map "r"    'hol-rotate)
(define-key hol-map "R"    'hol-restart-goal)
(define-key hol-map "s"    'send-string-to-hol)
(define-key hol-map "t"    'hol-toggle-show-types)
(define-key hol-map "u"    'hol-use-file)
