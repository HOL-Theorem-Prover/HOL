(module String-sig (lib "mlsig.scm" "lang")
  (provide String^)
  (require)
  (define-signature
   String^
   (maxSize size sub substring extract concat ^ str implode explode map translate tokens fields isPrefix compare collate fromString toString fromCString toCString < <= > >=)))
