# A simple `ThmSetData` example

This small example showcases some of the functionality of DIR.
To create, update, and eventually query a theorem set follow this steps:

* Using `export_with_ancestry` define the underlying data
  structure used in the theorems set, along with some basic
  functions to manipulate it. (`foobarLib.sml`).

* Import your theorem set definition and tag any theorems
  or definitions with its name (e.g. `[foobar]`).
  (`AScript.sml` and `BScript.sml`).

* To query the theorem set use its `get_global_value` function, or any
  other function in `AncestryData.fullresult`. (`CScript.sml`).
