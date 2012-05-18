signature Curl = sig
  val submitFile : {url : string, field : string, file : string} -> TextIO.instream
end
