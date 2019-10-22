structure Holmake_tools_dtype =
struct

datatype CodeType =
         Theory of string
       | Script of string
       | Other of string

datatype ArticleType =
         RawArticle of string
       | ProcessedArticle of string

datatype File =
         SML of CodeType
       | SIG of CodeType
       | UO of CodeType
       | UI of CodeType
       | ART of ArticleType
       | DAT of string
       | Unhandled of string

datatype 'dep buildcmds = Compile of 'dep list
                        | BuildScript of string * 'dep list
                        | BuildArticle of string * 'dep list
                        | ProcessArticle of string

end
