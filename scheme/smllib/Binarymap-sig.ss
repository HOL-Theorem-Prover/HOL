(module Binarymap-sig (lib "mlsig.scm" "lang")
  (provide Binarymap^)
  (require)
  (define-signature
   Binarymap^
   ((struct NotFound ()) mkDict insert find peek remove numItems listItems app revapp foldr foldl map transform)))
