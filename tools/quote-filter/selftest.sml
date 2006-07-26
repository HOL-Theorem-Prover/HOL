open OS.Process

val _ = system "./quote-filter input temp-output"

val result = system "diff temp-output desired-output"

val _ = if result = success then exit success else exit failure
