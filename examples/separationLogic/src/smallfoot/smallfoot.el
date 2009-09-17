(defun smallfoot-init ()
  "Initialises Smallfoot"
  (interactive)
  (hol ())
  (send-raw-string-to-hol 
   "PolyML.SaveState.loadState (Globals.HOLDIR ^ \"/examples/separationLogic/src/smallfoot/Smallfoot\");"
   nil nil))

(defun smallfoot-tactic (s)
  "*Executes a tactic*"
  (let* (
     (tac (concat "proofManagerLib.expand(" 
                   (concat s ") handle e => Raise e")))
     (sender (if hol-emit-time-elapsed-p
                     'send-timed-string-to-hol
                     'send-string-to-hol))
  ) (funcall sender tac hol-echo-commands-p)
    (hol-recentre)))

;; flags
(defvar smallfoot-autoconj-p nil "*do auto-conjs*")
(defun toggle-autoconj-p ()  
   "toggle the autoconj var"
   (interactive)
   (setq smallfoot-autoconj-p (not smallfoot-autoconj-p)))

(defvar smallfoot-autoclean-p nil "*do auto-clean*")
(defun toggle-autoclean-p ()  
   "toggle the autoclean var"
   (interactive)
   (setq smallfoot-autoclean-p (not smallfoot-autoclean-p)))

(defvar smallfoot-strictclean-p t "*do strict cleans*")
(defun toggle-strictclean-p ()  
   "toggle the strictclean var"
   (interactive)
   (setq smallfoot-strictclean-p (not smallfoot-strictclean-p)))

(defvar smallfoot-autopreprocess-p t "*do automatic preprocessing*")
(defun toggle-autopreprocess-p ()  
   "toggle the autopreprocess var"
   (interactive)
   (setq smallfoot-autopreprocess-p (not smallfoot-autopreprocess-p)))



(defvar smallfoot-case-split-p nil "*do automatic case splits*")
(defun toggle-case-split-p ()  
   "toggle the case-split var"
   (interactive)
   (setq smallfoot-case-split-p (not smallfoot-case-split-p))
   (setq smallfoot-guess-p (or smallfoot-guess-p smallfoot-case-split-p)))

(defvar smallfoot-guess-p t "*do automatic case splits*")
(defun toggle-guess-p ()  
   "toggle the guess-split var"
   (interactive)
   (setq smallfoot-guess-p (not smallfoot-guess-p))
   (setq smallfoot-case-split-p (and smallfoot-guess-p smallfoot-case-split-p)))


(defun smallfoot-set-default-flags ()  
   (setq smallfoot-case-split-p nil)
   (setq smallfoot-guess-p t)
   (setq smallfoot-autopreprocess-p t)
   (setq smallfoot-autoclean-p nil)
   (setq smallfoot-autoconj-p nil)
   (setq smallfoot-strictclean-p t))




(defun smallfoot-conj-clean-tactic (s)
  "*Executes a tactic and does cleaning*"
  (interactive "sTactic: ")
  (let* (
     (tac0 (concat "(" (concat s ")")))
     (tac1 (if smallfoot-autoconj-p (concat tac0 " THEN (REPEAT CONJ_TAC)") tac0))
     (tac2 (if smallfoot-autoclean-p (concat tac1 
               (if smallfoot-strictclean-p " THEN SMALLFOOT_STRICT_CLEAN_TAC" " THEN SMALLFOOT_CLEAN_TAC"))
            tac1))
  ) (smallfoot-tactic tac2)))



(defun smallfoot-spec-tac ()  
  "*Initialises a goal*"
  (interactive)
  (smallfoot-conj-clean-tactic "SMALLFOOT_SPECIFICATION_TAC"))


(defun smallfoot-loadfile (filename)
  "*Loads a new specification*"
  (interactive "fSpecification file: ")
  (send-string-to-hol
     (concat "val _ = dropn 200000;
              val _ = set_goal ([], parse_smallfoot_file \""
         (concat (expand-file-name filename) "\")")))
  (hol-print-goal)
  (if smallfoot-autopreprocess-p (smallfoot-spec-tac) ()))


(defun smallfoot-autofile (filename)
  "*Proves new specification*"
  (interactive "fSpecification file: ")
  (send-string-to-hol
     (concat "smallfoot_verbose_auto_prove \""
         (concat (expand-file-name filename) "\""))))




(defun case-split-guess-cases (tts fts ffs) 
   "split"
   (if smallfoot-guess-p 
      (if smallfoot-case-split-p tts fts)
      ffs))


(defun smallfoot-step-tac ()  
  "*Does one step*"
  (interactive)
  (smallfoot-conj-clean-tactic 
    (case-split-guess-cases 
       "SMALLFOOT_STEP_TAC []" 
       "SMALLFOOT_NO_CASE_SPLIT_STEP_TAC []" 
       "SMALLFOOT_NO_CASE_SPLIT_NO_GUESS_STEP_TAC []")))



(defun smallfoot-mini-step-tac ()  
  "*Does a mini step*"
  (interactive)
  (smallfoot-tactic 
    (case-split-guess-cases 
       "SMALLFOOT_MINI_STEP_TAC []" 
       "SMALLFOOT_NO_CASE_SPLIT_MINI_STEP_TAC []" 
       "SMALLFOOT_NO_CASE_SPLIT_NO_GUESS_MINI_STEP_TAC []")))

(defun smallfoot-solve-tac ()  
  "*tries to solve it*"
  (interactive)
  (smallfoot-tactic 
    (case-split-guess-cases 
       "SMALLFOOT_SOLVE_TAC []" 
       "SMALLFOOT_NO_CASE_SPLIT_SOLVE_TAC []" 
       "SMALLFOOT_NO_CASE_SPLIT_NO_GUESS_SOLVE_TAC []")))


(defun smallfoot-vc-step-tac ()  
  "*Does one step*"
  (interactive)
  (smallfoot-conj-clean-tactic "SMALLFOOT_VC_STEP_TAC"));

(defun smallfoot-vc-tac ()  
  "*Does one step*"
  (interactive)
  (smallfoot-conj-clean-tactic "SMALLFOOT_VC_TAC"));

(defun smallfoot-pure-step-tac ()  
  "*Does one step*"
  (interactive)
  (smallfoot-conj-clean-tactic "SMALLFOOT_STEP_TAC []"));


(defun conj-all-tac ()  
  "*Does split conjuctions*"
  (interactive)
  (smallfoot-tactic "REPEAT CONJ_TAC"))

(defun strip-all-tac ()  
  "*Does strip*"
  (interactive)
  (smallfoot-tactic "REPEAT STRIP_TAC"))

(defun smallfoot-clean-tac ()  
  "*Cleans up*"
  (interactive)
  (smallfoot-tactic 
      (if smallfoot-strictclean-p "SMALLFOOT_STRICT_CLEAN_TAC" "SMALLFOOT_CLEAN_TAC")))






;; my Menue and Keys
(define-prefix-command 'smallfoot-map)
(define-key global-map "\C-h" 'smallfoot-map)

(define-key-after (lookup-key global-map [menu-bar])
  [smallfoot]
  (cons "Smallfoot" (make-sparse-keymap "Smallfoot"))
  'hol-menu)

(define-key smallfoot-map "V" 'smallfoot-vc-tac)
(define-key global-map [menu-bar smallfoot vc_solve_tac]
   '("VC Solve" . smallfoot-vc-tac))

(define-key smallfoot-map "S" 'smallfoot-solve-tac)
(define-key global-map [menu-bar smallfoot solve_tac]
   '("Solve" . smallfoot-solve-tac))

(define-key global-map [menu-bar smallfoot pure_step_tac]
   '("Pure Step" . smallfoot-pure-step-tac))

(define-key smallfoot-map "v" 'smallfoot-vc-step-tac)
(define-key global-map [menu-bar smallfoot vc_step_tac]
   '("VC Step" . smallfoot-vc-step-tac))

(define-key smallfoot-map "s" 'smallfoot-step-tac)
(define-key global-map [menu-bar smallfoot step_tac]
   '("Step" . smallfoot-step-tac))

(define-key smallfoot-map "m" 'smallfoot-mini-step-tac)
(define-key global-map [menu-bar smallfoot mini_step_tac]
   '("Mini Step" . smallfoot-mini-step-tac))

(define-key global-map [menu-bar smallfoot sep5]
   '(menu-item "--"))

(define-key global-map [menu-bar smallfoot options]
    (cons "Options" (make-sparse-keymap "Options")))   

(define-key global-map [menu-bar smallfoot options auto-case-split]
   '(menu-item "case splits" toggle-case-split-p
                     :button (:toggle
                              . (and (boundp 'smallfoot-case-split-p)
                                     smallfoot-case-split-p))))

(define-key global-map [menu-bar smallfoot options auto-guess]
   '(menu-item "guess instantiations" toggle-guess-p
                     :button (:toggle
                              . (and (boundp 'smallfoot-guess-p)
                                     smallfoot-guess-p))))

(define-key global-map [menu-bar smallfoot options sep4]
   '(menu-item "--"))

(define-key global-map [menu-bar smallfoot options set_defaults]
   '("Reset to Defaults" . smallfoot-set-default-flags))

(define-key global-map [menu-bar smallfoot  options  auto-preprocess]
   '(menu-item "auto preprocessing" toggle-autopreprocess-p
                     :button (:toggle
                              . (and (boundp 'smallfoot-autopreprocess-p)
                                     smallfoot-autopreprocess-p))))

(define-key global-map [menu-bar smallfoot  options  strict-clean]
   '(menu-item "strict cleaning" toggle-strictclean-p
                     :button (:toggle
                              . (and (boundp 'smallfoot-strictclean-p)
                                     smallfoot-strictclean-p))))

(define-key global-map [menu-bar smallfoot  options  auto-clean]
   '(menu-item "auto clean" toggle-autoclean-p
                     :button (:toggle
                              . (and (boundp 'smallfoot-autoclean-p)
                                     smallfoot-autoclean-p))))


(define-key global-map [menu-bar smallfoot options auto-conj]
   '(menu-item "auto conjunctions" toggle-autoconj-p
                     :button (:toggle
                              . (and (boundp 'smallfoot-autoconj-p)
                                     smallfoot-autoconj-p))))

(define-key global-map [menu-bar smallfoot goalstack]
    (cons "Goalstack" (make-sparse-keymap "Goalstack")))   
(define-key smallfoot-map "C" 'smallfoot-clean-tac)
(define-key global-map [menu-bar smallfoot goalstack clean_tac]
   '("Clean" . smallfoot-clean-tac))
(define-key smallfoot-map "t" 'strip-all-tac)
(define-key global-map [menu-bar smallfoot goalstack strip_tac]
   '("Strip" . strip-all-tac))
(define-key smallfoot-map "c" 'smallfoot-clean-tac)
(define-key global-map [menu-bar smallfoot goalstack conj_tac]
   '("Conjuncts" . conj-all-tac))
(define-key global-map [menu-bar smallfoot goalstack restart]
   '("Restart" . hol-restart-goal))
(define-key global-map [menu-bar smallfoot goalstack drop]
   '("Drop" . hol-drop-goal))
(define-key smallfoot-map "b" 'backup_tac)
(define-key global-map [menu-bar smallfoot goalstack backup_tac]
   '("Undo (Backup)" . hol-backup))
(define-key global-map [menu-bar smallfoot sep2]
   '(menu-item "--"))
(define-key smallfoot-map "p" 'smallfoot-spec-tac)
(define-key global-map [menu-bar smallfoot spec_tac]
   '("Preprocess" . smallfoot-spec-tac))
(define-key smallfoot-map "L" 'smallfoot-autofile)
(define-key global-map [menu-bar smallfoot autoload]
   '("Auto-prove Specification" . smallfoot-autofile))
(define-key smallfoot-map "l" 'smallfoot-loadfile)
(define-key global-map [menu-bar smallfoot load]
   '("Load Specification" . smallfoot-loadfile))
(define-key global-map [menu-bar smallfoot sep1]
   '(menu-item "--"))
(define-key global-map [menu-bar smallfoot init]
   '("Initialise Smallfoot" . smallfoot-init))




