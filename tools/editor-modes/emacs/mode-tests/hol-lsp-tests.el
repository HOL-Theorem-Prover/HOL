;;; run with something like
;;;  HOLDIR=<dir> emacs -batch -l ert -l hol-lsp-tests.el \
;;;                     -f ert-run-tests-batch-and-exit

(load (concat (file-name-as-directory (getenv "HOLDIR"))
              "tools/editor-modes/emacs/hol-mode"))

(defun hol-lsp-tests--setup-alternate-install (root)
  "Symlink ROOT/bin/{hol,Holmake} to the current install's binaries
so routing tests can stage a second HOL without a real build."
  (make-directory (concat root "/bin") t)
  (make-symbolic-link hol-executable (concat root "/bin/hol") t)
  (make-symbolic-link (concat (file-name-directory hol-executable)
                              "Holmake")
                      (concat root "/bin/Holmake") t))

(defun hol-lsp-tests--drop-lastmaker (dir hol-root)
  "Write DIR/.hol/make-deps/lastmaker naming HOL-ROOT/bin/Holmake."
  (let ((path (concat dir "/.hol/make-deps/lastmaker")))
    (make-directory (file-name-directory path) t)
    (with-temp-file path
      (insert (concat hol-root "/bin/Holmake\n")))))

(defmacro hol-lsp-tests--with-alt-install (holX-var workdir-var &rest body)
  "Bind HOLX-VAR to a fresh symlink-install root, WORKDIR-VAR to
a workdir under it whose lastmaker points at HOLX-VAR, clear the
LSP caches, run BODY, tear down."
  (declare (indent 2))
  `(let* ((,holX-var (make-temp-file "hol-lsp-holX-" t))
          (,workdir-var (concat ,holX-var "/src/foo/")))
     (unwind-protect
         (progn
           (hol-lsp-tests--setup-alternate-install ,holX-var)
           (make-directory ,workdir-var t)
           (hol-lsp-tests--drop-lastmaker ,workdir-var ,holX-var)
           (clrhash hol-lsp--hol-cache)
           (clrhash hol-lsp--heap-cache)
           ,@body)
       (delete-directory ,holX-var t))))

(ert-deftest hol-lsp-routes-via-lastmaker ()
  (hol-lsp-tests--with-alt-install holX workdir
    (should (equal (hol-lsp--hol-for-dir workdir)
                   (concat holX "/bin/hol")))))

(ert-deftest hol-lsp-falls-back-without-lastmaker ()
  (let ((workdir (make-temp-file "hol-lsp-nolm-" t)))
    (unwind-protect
        (progn
          (clrhash hol-lsp--hol-cache)
          (should (equal (hol-lsp--hol-for-dir workdir)
                         hol-executable)))
      (delete-directory workdir t))))

(ert-deftest hol-lsp-different-installs-different-projects ()
  (let* ((holX (make-temp-file "hol-lsp-holX-" t))
         (holY (make-temp-file "hol-lsp-holY-" t))
         (workX (concat holX "/src/foo/"))
         (workY (concat holY "/src/foo/")))
    (unwind-protect
        (progn
          (hol-lsp-tests--setup-alternate-install holX)
          (hol-lsp-tests--setup-alternate-install holY)
          (make-directory workX t)
          (make-directory workY t)
          (hol-lsp-tests--drop-lastmaker workX holX)
          (hol-lsp-tests--drop-lastmaker workY holY)
          (clrhash hol-lsp--hol-cache)
          (clrhash hol-lsp--heap-cache)
          (let* ((pX (with-temp-buffer
                       (setq buffer-file-name
                             (concat workX "fooScript.sml"))
                       (setq major-mode (car hol-lsp-server-modes))
                       (let ((default-directory workX))
                         (hol-lsp--project-try workX))))
                 (pY (with-temp-buffer
                       (setq buffer-file-name
                             (concat workY "fooScript.sml"))
                       (setq major-mode (car hol-lsp-server-modes))
                       (let ((default-directory workY))
                         (hol-lsp--project-try workY)))))
            (should pX)
            (should pY)
            (should-not (equal pX pY))))
      (delete-directory holX t)
      (delete-directory holY t))))

(defun hol-lsp-tests--project-for (dir file)
  "The project object `hol-lsp--project-try' yields for FILE in DIR."
  (with-temp-buffer
    (setq buffer-file-name (concat dir file))
    (setq major-mode (car hol-lsp-server-modes))
    (let ((default-directory dir))
      (hol-lsp--project-try dir))))

(ert-deftest hol-lsp-each-buffer-gets-its-own-project ()
  "Two scripts in ONE directory must not share a project, and so must
not share a server: a server is bound to the first file it compiles,
because loading a theory seals it and a second file's ancestors can
then neither be re-read nor withdrawn."
  (let ((dir (file-name-as-directory
              (make-temp-file "hol-lsp-perbuf-" t))))
    (unwind-protect
        (progn
          (clrhash hol-lsp--hol-cache)
          (clrhash hol-lsp--heap-cache)
          (let ((pA (hol-lsp-tests--project-for dir "aScript.sml"))
                (pB (hol-lsp-tests--project-for dir "bScript.sml")))
            (should pA)
            (should pB)
            (should-not (equal pA pB))))
      (delete-directory dir t))))

(ert-deftest hol-lsp-same-file-shares-one-project ()
  "Two buffers visiting the SAME file are still one file, so they
share a server."
  (let ((dir (file-name-as-directory
              (make-temp-file "hol-lsp-perbuf-" t))))
    (unwind-protect
        (progn
          (clrhash hol-lsp--hol-cache)
          (clrhash hol-lsp--heap-cache)
          (should (equal (hol-lsp-tests--project-for dir "aScript.sml")
                         (hol-lsp-tests--project-for dir "aScript.sml"))))
      (delete-directory dir t))))

(ert-deftest hol-lsp-project-root-is-the-files-own-directory ()
  "eglot spawns the server with cwd = project root, and
`get_heap_name' reads the Holmakefile there, so the root must be the
file's own directory -- not a VC root, and not the file itself."
  (require 'project)
  (let ((dir (file-name-as-directory
              (make-temp-file "hol-lsp-perbuf-" t))))
    (unwind-protect
        (progn
          (clrhash hol-lsp--hol-cache)
          (clrhash hol-lsp--heap-cache)
          (let ((p (hol-lsp-tests--project-for dir "aScript.sml")))
            (should (equal (project-root p) dir))
            (should (equal (project-name p) "aScript.sml"))))
      (delete-directory dir t))))

(ert-deftest hol-lsp-server-program-uses-resolved-hol ()
  (hol-lsp-tests--with-alt-install holX workdir
    (let ((default-directory workdir))
      (should (equal (hol-lsp--server-program)
                     (list (concat holX "/bin/hol") "lsp"))))))

;;; --- *HOL Goals* presentation ------------------------------------

(ert-deftest hol-lsp-context-line-is-nil-when-empty ()
  (should (equal (hol-lsp--context-line nil) nil))
  (should (equal (hol-lsp--context-line []) nil)))

(ert-deftest hol-lsp-context-line-brackets-each-tag ()
  ;; eglot hands JSON arrays over as vectors, so both must work.
  (should (equal (hol-lsp--context-line ["inside >-"]) "[inside >-]"))
  (should (equal (hol-lsp--context-line '("branch 2 of 3 of THENL"
                                          "inside 2 nested >-"))
                 "[branch 2 of 3 of THENL] [inside 2 nested >-]")))

(ert-deftest hol-lsp-goals-header-carries-the-identifying-bits ()
  (let ((h (hol-lsp--goals-header
            '(:theorem "foo" :step 7 :context ["inside >-"] :error nil))))
    (should (string-match-p "foo" h))
    (should (string-match-p "step 7" h))
    (should (string-match-p (regexp-quote "[inside >-]") h))))

(ert-deftest hol-lsp-goals-header-includes-the-error ()
  (should (string-match-p
           "⚠ boom"
           (hol-lsp--goals-header
            '(:theorem "foo" :step 0 :context nil :error "boom")))))

(ert-deftest hol-lsp-goals-header-escapes-percent ()
  ;; A header-line string is read for mode-line constructs, so a `%'
  ;; coming from a theorem name or an error must not be one.
  (should (equal (hol-lsp--goals-header
                  '(:theorem "a%b" :step 0 :context nil :error nil))
                 "a%%b — step 0")))

(ert-deftest hol-lsp-strip-context-removes-the-repeated-line ()
  ;; `pretty' repeats the tags at its top; the buffer shows only the
  ;; goals, the tags having moved to the header line.
  (should (equal (hol-lsp--strip-context
                  "[inside >-]\n\n\n 0.  asm\n----\n     goal\n"
                  ["inside >-"])
                 " 0.  asm\n----\n     goal\n")))

(ert-deftest hol-lsp-strip-context-leaves-the-goal-text-alone ()
  ;; Leading blank lines go; the goal itself does not.
  (should (equal (hol-lsp--strip-context "\n[] = []\n" nil) "[] = []\n"))
  ;; A goal starting with `[' is not a tag line: matching the exact
  ;; string the server sent is what tells them apart.
  (should (equal (hol-lsp--strip-context "[] = []\n" ["inside >-"])
                 "[] = []\n")))

(ert-deftest hol-lsp-goals-header-flags-a-solved-focus ()
  ;; `pretty' announces this on its first line, which scrolling to the
  ;; end carries out of sight — so the header has to carry it.
  (should (string-match-p
           "✓ solved"
           (hol-lsp--goals-header
            '(:theorem "foo" :step 3 :context ["inside >-"]
              :goals [] :error nil))))
  (should (hol-lsp--solved-p '(:goals [] :error nil)))
  (should (hol-lsp--solved-p '(:goals nil :error nil)))
  ;; A reply with no `goals' field at all is not a solved focus.
  (should-not (hol-lsp--solved-p '(:error nil))))

(ert-deftest hol-lsp-goals-header-does-not-flag-a-timeout ()
  ;; A timeout has no goals either, but it is not a proved subgoal.
  (let ((r '(:theorem "foo" :step 3 :context nil
             :goals [] :error "walker timed out")))
    (should-not (hol-lsp--solved-p r))
    (should-not (string-match-p "✓ solved" (hol-lsp--goals-header r)))
    (should (string-match-p "⚠ walker timed out"
                            (hol-lsp--goals-header r)))))

(ert-deftest hol-lsp-goals-header-does-not-flag-an-ordinary-state ()
  (let ((r '(:theorem "foo" :step 3 :context nil
             :goals [(:asms [] :goal "a = a")] :error nil)))
    (should-not (hol-lsp--solved-p r))
    (should-not (string-match-p "✓ solved" (hol-lsp--goals-header r)))))

(ert-deftest hol-lsp-goals-go-below-a-narrow-window ()
  (with-temp-buffer
    (let ((hol-lsp-goals-side-min-width 160))
      ;; batch frames are 80 columns, well under the threshold
      (should (memq 'display-buffer-below-selected
                    (car (hol-lsp--goals-display-action)))))))

(ert-deftest hol-lsp-goals-go-beside-a-wide-window ()
  (with-temp-buffer
    (let ((hol-lsp-goals-side-min-width 10))   ; force the wide branch
      (let ((action (hol-lsp--goals-display-action)))
        (should (memq 'display-buffer-in-direction (car action)))
        (should (eq 'right (cdr (assq 'direction action))))))))

(ert-deftest hol-lsp-goals-side-split-can-be-switched-off ()
  (with-temp-buffer
    (let ((hol-lsp-goals-side-min-width nil))
      (should (memq 'display-buffer-below-selected
                    (car (hol-lsp--goals-display-action)))))))

(ert-deftest hol-lsp-uri-round-trips-to-a-path ()
  (let ((path (make-temp-file "hol-lsp-uri-")))
    (unwind-protect
        (should (equal (hol-lsp--uri-to-path (hol-lsp--path-to-uri path))
                       path))
      (delete-file path))))

(ert-deftest hol-lsp-blocked-marks-the-buffer-visiting-the-uri ()
  "`$/compileBlocked\' names a file; the flag belongs to its buffer."
  (let* ((path (make-temp-file "hol-lsp-blocked-" nil "Script.sml"))
         (buf (find-file-noselect path)))
    (unwind-protect
        (progn
          (hol-lsp--set-blocked (hol-lsp--path-to-uri path)
                                "cannot load fooTheory")
          (should (equal (buffer-local-value 'hol-lsp--blocked buf)
                         "cannot load fooTheory"))
          (hol-lsp--set-blocked (hol-lsp--path-to-uri path) nil)
          (should-not (buffer-local-value 'hol-lsp--blocked buf)))
      (kill-buffer buf)
      (delete-file path))))

(ert-deftest hol-lsp-blocked-for-an-unvisited-file-is-quiet ()
  (should-not (hol-lsp--set-blocked "file:///no/such/file/Script.sml" "x")))

(ert-deftest hol-lsp-goalstate-params-carry-a-width ()
  "The server renders at the width we ask for, so the request has to
carry one."
  (with-temp-buffer
    (setq buffer-file-name "/tmp/widthScript.sml")
    (let ((params (hol-lsp--goalstate-params)))
      (should (integerp (plist-get params :width)))
      (should (>= (plist-get params :width) 20)))))

(ert-deftest hol-lsp-goals-width-never-goes-below-the-floor ()
  "A sliver of a window would otherwise ask for a width HOL cannot
break at."
  (should (>= (hol-lsp--goals-width) 20)))

(ert-deftest hol-lsp-proof-summary-is-quiet-when-there-is-nothing ()
  "A session with checking off must not put anything in the mode line."
  (with-temp-buffer
    (should (equal (hol-lsp-proof-summary) ""))))

(ert-deftest hol-lsp-proof-summary-counts-the-pool ()
  "The counter is the ordering-independent signal: proofs settle in
whatever order the workers finish, so what answers \"is it done?\" is
the tally, not the per-proof marks."
  (with-temp-buffer
    (setq hol-lsp--proof-states (make-hash-table :test #'equal))
    (puthash "a" "proved" hol-lsp--proof-states)
    (puthash "b" "checking" hol-lsp--proof-states)
    (should (equal (hol-lsp-proof-summary) " HOL[1/2]"))
    (puthash "b" "proved" hol-lsp--proof-states)
    (should (equal (hol-lsp-proof-summary) " HOL[2 ok]"))
    (puthash "c" "failed" hol-lsp--proof-states)
    (should (equal (hol-lsp-proof-summary) " HOL[2/3 1!]"))))

(ert-deftest hol-lsp-proof-states-accumulate-and-cheated-drops ()
  "`$/proofStates' is a transition stream, so the client accumulates.
A `cheated' state means the pool has dropped the entry -- an edit
reached that proof -- and it stops being an outcome rather than
counting as one."
  (let ((file (make-temp-file "holproofs" nil "Script.sml")))
    (unwind-protect
        (let ((buf (find-file-noselect file)))
          (with-current-buffer buf
            (hol-lsp--note-proof-states
             (hol-lsp--path-to-uri file)
             (list (list :name "t1" :status "checking")
                   (list :name "t2" :status "checking")))
            (should (equal (hol-lsp-proof-summary) " HOL[0/2]"))
            (hol-lsp--note-proof-states
             (hol-lsp--path-to-uri file)
             (list (list :name "t1" :status "proved")))
            (should (equal (hol-lsp-proof-summary) " HOL[1/2]"))
            (hol-lsp--note-proof-states
             (hol-lsp--path-to-uri file)
             (list (list :name "t2" :status "cheated")))
            (should (equal (hol-lsp-proof-summary) " HOL[1 ok]")))
          (kill-buffer buf))
      (delete-file file))))
