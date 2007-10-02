(module Binaryset-sig (lib "mlsig.scm" "lang")
  (provide Binaryset^)
  (require)
  (define-signature
   Binaryset^
   ((struct NotFound ())
    empty
    singleton
    add
    addList
    retrieve
    peek
    isEmpty
    equal
    isSubset
    member
    delete
    numItems
    union
    intersection
    difference
    listItems
    app
    revapp
    foldr
    foldl
    find)))
