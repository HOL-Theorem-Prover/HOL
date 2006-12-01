signature AssembleDiskFiles =
sig
  val raw_read_stream : TextIO.instream -> DiskFilesHeader.parse_result
  val raw_read_file : string -> DiskFilesHeader.parse_result
end
