fun emacs_hol_mode_loaded () =
   ["HOL_Interactive", "Meta",
  "Array", "ArraySlice", "BinIO", "BinPrimIO", "Bool", "Byte",
  "CharArray", "CharArraySlice", "Char", "CharVector",
  "CharVectorSlice", "CommandLine.name", "Date", "General", "IEEEReal",
  "Int", "IO", "LargeInt", "LargeReal", "LargeWord", "List", "ListPair",
  "Math", "Option", "OS", "Position", "Real", "StringCvt", "String",
  "Substring", "TextIO", "TextPrimIO", "Text", "Timer", "Time",
  "VectorSlice", "Vector", "Word8Array", "Word8ArraySlice",
  "Word8Vector", "Word8VectorSlice", "Word8", "Word"] @ (Meta.loaded());
