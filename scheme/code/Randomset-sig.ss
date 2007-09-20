(module Randomset-sig (lib "mlsig.scm" "lang")
  (provide Randomset^)
  (require)
  (define-signature
   Randomset^
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
