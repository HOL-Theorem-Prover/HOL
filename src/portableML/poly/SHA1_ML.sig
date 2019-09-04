signature SHA1_ML =
sig
  (* A reader assumes a stream or function view of IO. A reader function
   * takes in stream state and an positive integer n specifying the number
   * of bytes to read. It returns a vector of n bytes and a new stream
   * state. The reader should only return less than n bytes if the stream
   * has ended and n bytes are not available. An input of 0 bytes should
   * always return an empty vector and cannot be used to check for the end
   * of the stream.
   *)
  type 'a byte_reader = 'a * int -> Word8Vector.vector * 'a

  val sha1 : 'a byte_reader -> 'a -> Word8Vector.vector
  val sha1String : 'a byte_reader -> 'a -> string
  val sha1_file : {filename: string} -> string

end
