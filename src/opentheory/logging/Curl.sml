structure Curl :> Curl = struct
  fun submitFile {url,field,file} = let
    open OS.Process
    val t = OS.FileSys.tmpName()
    val _ = if isSuccess(system("curl -F '"^field^"=@"^file^"' '"^url^"' >"^t)) then ()
            else raise mk_HOL_ERR "Curl" "submitFile" "curl call failed"
  in TextIO.openIn t end
end
