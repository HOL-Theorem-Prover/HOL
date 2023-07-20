structure Holmake_tools_dtype =
struct

datatype ('dep,'extra) buildcmds =
         Compile of 'dep list * 'extra
       | BuildScript of string * 'dep list * 'extra
       | BuildArticle of string * 'dep list * 'extra
       | ProcessArticle of string * 'extra

end
