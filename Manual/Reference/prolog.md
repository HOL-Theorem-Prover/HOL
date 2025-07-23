---
header-includes: |
  \input{../LaTeX/commands}
  \input{ref-unicode}
  \usepackage{titlesec}
  \usepackage[english]{babel}
  \usepackage{underscore}
  \newcommand{\currentstruct}{}
  \newcommand{\mysec}[1]{%
    \makebox[\linewidth]{%
      \fbox{%
        \makebox[\dimexpr\linewidth-2\fboxsep][l]{\strut\hspace{0.4em}#1\hfill(\texttt{\currentstruct})\hspace{0.2em}}%
      }%
    }}
  \titleformat{\section}{\normalfont\LARGE}{}{0pt}{\mysec}
  \usepackage[a4paper,width=160truemm,height=225truemm,top=38mm,
              headheight=16pt,headsep=20pt,footskip=13mm]{geometry}
  \renewcommand{\rmdefault}{bch}
  \usepackage{microtype}
  \DisableLigatures{encoding = T1, family = tt*}
---

\include{title}
\include{preface}
\input{../LaTeX/ack}

# Entries
