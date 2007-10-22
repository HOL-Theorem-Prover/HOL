(module FileSys-sig (lib "mlsig.scm" "lang")
  (provide FileSys^)
  (require)
  (define-signature
   FileSys^
   (openDir
     readDir
     rewindDir
     closeDir
     chDir
     getDir
     mkDir
     rmDir
     isDir
     realPath
     fullPath
     isLink
     readLink
     modTime
     setTime
     remove
     rename
     (struct A_READ (content))
     access
     fileSize
     tmpName
     fileId
     hash
     compare)))
