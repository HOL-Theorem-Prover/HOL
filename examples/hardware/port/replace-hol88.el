;;; replace-hol88.el --- Helpers for porting hol88 code -*- lexical-binding: t -*-

(defun replace-hol88 ()
  "some simple string replacements that help with porting hol88 code"
  (interactive)
  (goto-char 0)
  (replace-string "\"" "___A___")
  (goto-char 0)
  (replace-string "`" "\"")
  (goto-char 0)
  (replace-string "___A___" "``")
  (goto-char 0)
  (replace-string ";;" ";")
  (goto-char 0)
  (replace-string "let" "val")
  (goto-char 0)
  (replace-string "%" "(*")
  )

