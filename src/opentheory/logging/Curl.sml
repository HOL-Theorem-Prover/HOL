structure Curl :> Curl = struct
  fun submitFile {url,field,file} = let
    open OS.Process
    val t = OS.FileSys.tmpName()
    val _ = if isSuccess(system("curl -sSH'Expect:' -F'"^field^"=@"^file^"' '"^url^"' >"^t)) then ()
            else raise Feedback.mk_HOL_ERR "Curl" "submitFile" "curl call failed"
  in TextIO.openIn t end
end
