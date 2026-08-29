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
           (clrhash hol-lsp--project-roots)
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
          (clrhash hol-lsp--project-roots)
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

(ert-deftest hol-lsp-server-program-uses-resolved-hol ()
  (hol-lsp-tests--with-alt-install holX workdir
    (let ((default-directory workdir))
      (should (equal (hol-lsp--server-program)
                     (list (concat holX "/bin/hol") "lsp"))))))
