# doc-to-tex.sed: A sed script that transforms a <thing>.doc file into
#                 tex source code for a reference manual entry on <thing>
# Top 2 lines added to scrub Library and Keywords paragraphs    [JRH 91.08.15]
# Lines for BLTYPE and ELTYPE added to deal with long types     [RJB 91.09.24]
# Ugly hack to deal with 2n+1 adjacent braces added             [JRH 91.10.02]
# put begin and end verbatim in separate lines                  [WW  93.07.20]
/^\\KEYWORDS/,/^ *$/d
/^\\LIBRARY/,/^ *$/d
s/qr/qqr/g; s/~/pqr/g;
s/{{/~/g; s/\(~*\){/{\1/g; s/~/<<<<<</g;
s/pqr/~/g; s/qqr/qr/g;
s/}}/>>>>>>/g;
s/{/{\\small\\verb%/g;
s/}/%}/g;
s/^{\\small\\verb%[ ]*$/{\\par\\samepage\\setseps\\small\
\\begin{verbatim}/g;
s/^%}[ ]*$/\\end{verbatim}\
}/g;
/\\DOC.*/s/_/\\_/g;
/\\DOC.*/s/.DOC[ ]*/\\DOC{/g;
/\\DOC.*/s/$/}/g;
/\\TYPE.*/s/$/\\egroup/g;
/\\BLTYPE.*/s/\\BLTYPE[ ]*/{\\small\
\\begin{verbatim}/g;
/\\ELTYPE.*/s/\\ELTYPE[ ]*/\\end{verbatim}\
}\\egroup/g;
/\\THEOREM.*/s/_/\\_/g;
/\\THEOREM.*/s/\\none/{\\none}/g;
s/<<<<<</{/g;
s/>>>>>>/}/g;
