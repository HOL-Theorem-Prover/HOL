hook global KakBegin .* %{

hook global BufCreate .*Script\.sml %{
    set-option buffer filetype holscript
}

}

hook global WinSetOption filetype=holscript %{
    require-module hol
    set buffer indentwidth 2

    hook window ModeChange pop:insert:.* -group hol-trim-indent hol-trim-indent
    hook window InsertChar .* -group hol-indent hol-indent-on-char
    hook window InsertChar \n -group hol-indent hol-indent-on-new-line
}

hook -group holscript-highlight global WinSetOption filetype=holscript %{
    add-highlighter window/ini ref holscript
    hook -once -always window WinSetOption filetype=.* %{ remove-highlighter window/holscript }
}


provide-module hol %{


require-module sml

declare-option -hidden str holfifodir
declare-option -hidden str holfifo

hook global KakEnd .* hol-close

define-command hol-start -docstring '
hol-start: start HOL instance in new terminal window, from HOLDIR' %{
    hook global BufOpenFile .*Script\.sml hol-load-deps-current
    hol-close
    evaluate-commands %sh{
        holfifodir=$(mktemp -d /tmp/kak-fifo.XXXXXXXX)
        mkfifo $holfifodir/fifo
        printf "set-option current holfifodir '%s'" "$holfifodir"
    }
    set-option current holfifo %sh{printf "%s/fifo" "$kak_opt_holfifodir"}
    terminal sh -i -c %sh{
        printf "%s\n\n" "cat > $kak_opt_holfifo & echo \$! > $kak_opt_holfifodir/pid & (tee -i >($HOLDIR/bin/hol --zero)) < $kak_opt_holfifo"
    }

    hol-load-deps-all
}

define-command hol-send -docstring '
hol-send: send selection verbatim to HOL' %{
    nop %sh{printf "%s\n\0" "$kak_selection" > "$kak_opt_holfifo"}
}

define-command hol-goal-send -docstring '
hol-goal-send: send selection as new goal to HOL' %{
    nop %sh{printf "g(\`%s\`);\n\0" "$kak_selection" > "$kak_opt_holfifo"}
}

define-command hol-tactic -docstring '
hol-tactic: send selection as tactic to HOL' %{
    nop %sh{printf "e(%s);\n\0" "$kak_selection" > "$kak_opt_holfifo"}
}

define-command hol-show-goal -docstring '
hol-show-goal: show current goal in HOL' %{
    nop %sh{printf "p();\n\0" > "$kak_opt_holfifo"}
}

define-command hol-backup -docstring '
hol-backup: step back in proof in HOL' %{
    nop %sh{printf "b();\n\0" > "$kak_opt_holfifo"}
}

define-command hol-drop -docstring '
hol-drop: drop goal in HOL' %{
    nop %sh{printf "drop();\n\0" > "$kak_opt_holfifo"}
}

define-command hol-rotate -docstring '
hol-rotate <n>: rotate subgoals n times in HOL' -params 1 %{
    nop %sh{printf "r $1;\n\0" > "$kak_opt_holfifo"}
}

define-command hol-restart-proof -docstring '
hol-restart-proof: restart proof in HOL' %{
    nop %sh{printf "restart();\n\0" > "$kak_opt_holfifo"}
}

define-command hol-load-deps-for -docstring '
hol-load-deps-for: load dependencies for a HOL file' -params 1 %{
    nop %sh{
        $HOLDIR/bin/holdeptool.exe $1 | sed 's/.*/qload "&" handle _ => (); /' > "$kak_opt_holfifo"
    }
}

define-command hol-load-deps-all -docstring '
hol-load-deps-for: load dependencies for all open HOL files' %{
    nop %sh{
        eval set -- "$kak_quoted_buflist"
        while [ $# -gt 0 ]; do
            $HOLDIR/bin/holdeptool.exe $1 | sed 's/.*/qload "&" handle _ => (); /' > "$kak_opt_holfifo"
            shift
        done
    }
}

define-command hol-load-deps-current -docstring '
hol-load-deps-current: load dependencies for current buffer HOL file' %{hol-load-deps-for %val{buffile}}

define-command hol-close -docstring '
hol-close: close current HOL session' %{
    nop %sh{
        cat $kak_opt_holfifodir/pid | xargs kill -9
    }
}


set-face global cheat red,default,red+u
set-face global binders bright-blue,default,default
set-face global indrules bright-blue,default,bright-blue+u
set-face global listsep white,default,default

add-highlighter shared/holsyntax group
add-highlighter shared/holsyntax/ ref sml
# custom regex hightlighting must come after ref to override
add-highlighter shared/holsyntax/ regex '\b(Definition|(Co)?Inductive|Datatype|Theorem|Triviality|End|Termination|Proof|QED|Type|Overload)\b' 0:keyword
add-highlighter shared/holsyntax/ regex '^\[(~?\w+):\]' 1:indrules
add-highlighter shared/holsyntax/ regex '\bcheat\b' 0:cheat

add-highlighter shared/newholsyntax regions
add-highlighter shared/newholsyntax/ region '^(Definition|(Co)?Inductive|Datatype|Theorem|Triviality)' ':\W*$' ref holsyntax
add-highlighter shared/newholsyntax/ region '^(End|Termination|Proof)' '.' ref holsyntax
add-highlighter shared/newholsyntax/ region '^\[~?\w+:\]' '.' ref holsyntax
add-highlighter shared/newholsyntax/ default-region ref quotedhol

add-highlighter shared/quotedhol regions
# must specify strings and comments before regions to prevent binders escaping
add-highlighter shared/quotedhol/comment region -recurse '\(\*' '\(\*' '\*\)' fill comment
add-highlighter shared/quotedhol/string region '"' '"' fill string
add-highlighter shared/quotedhol/bind region '!|∀|\?|∃|(?<!\\)(?<!/)\\(?!\\)(?!/)|λ' '\.' regions
add-highlighter shared/quotedhol/bind/ region -recurse '\(\*' '\(\*' '\*\)' fill comment
add-highlighter shared/quotedhol/bind/code default-region group
add-highlighter shared/quotedhol/bind/code/ fill binders
add-highlighter shared/quotedhol/bind/code/ regex '!|∀|\?|∃|\\|λ|\.' 0:operator
add-highlighter shared/quotedhol/terms default-region group
add-highlighter shared/quotedhol/terms/ ref sml
# custom regex hightlighting must come after ref to override
add-highlighter shared/quotedhol/terms/ regex '`(?!`)|‘|’|``(?!`)|“|”' 0:meta
add-highlighter shared/quotedhol/terms/ regex '∧|∨|¬|⇒|≤|≥|⇔|≠|∈|∉|∩|∪|⊆|⊂|\b(IN|NOTIN|INTER|UNION|DIFF|SUBSET|PSUBSET|EMPTY)\b' 0:operator
add-highlighter shared/quotedhol/terms/ regex ';' 0:listsep

add-highlighter shared/holscript regions
add-highlighter shared/holscript/ region '^Definition.*:\W*$' '^(End|Termination)\W*$' ref newholsyntax
add-highlighter shared/holscript/ region '^(Datatype|(Co)?Inductive).*:\W*$' '^End\W*$' ref newholsyntax
add-highlighter shared/holscript/ region '^(Theorem|Triviality).*:\W*$' '^Proof\W*$' ref newholsyntax
add-highlighter shared/holscript/ region '`(?!`)' '`' ref quotedhol
add-highlighter shared/holscript/ region '‘' '’' ref quotedhol
add-highlighter shared/holscript/ region '``(?!`)' '``' ref quotedhol
add-highlighter shared/holscript/ region '“' '”' ref quotedhol
add-highlighter shared/holscript/comment region -recurse '\(\*' '\(\*' '\*\)' fill comment
add-highlighter shared/holscript/code default-region ref holsyntax


define-command -hidden hol-trim-indent %{
    # remove trailing white spaces
    try %{ execute-keys -draft -itersel x s \h+$ <ret> d }
}

define-command -hidden hol-indent-on-char %{
    evaluate-commands -draft -itersel %{
        # align closer token to its opener when alone on a line
        try %{ execute-keys -draft <a-h> <a-k> ^\h+[\]\)]$ <ret> m s \A|.\z <ret> 1<a-&> }
        # align HOL syntax to start
        try %{ execute-keys -draft <a-h> <a-k> ^\h+(Proof|Termination|QED|End) <ret> x s ^\h+ <ret> d }
    }
}

define-command -hidden hol-indent-on-new-line %{
    evaluate-commands -draft -itersel %{
        # preserve previous line indent
        try %{ execute-keys -draft <semicolon> K <a-&> }
        # filter previous line
        try %{ execute-keys -draft k : hol-trim-indent <ret> }
        # indent after lines beginning / ending with opener token
        try %{ execute-keys -draft k x <a-k> [[\(]\h*$|^(Definition|(Co)?Inductive|Datatype|Theorem|Triviality).*:\W*$|^(Proof|Termination).*$|^\[~?\w+:\].*$ <ret> j <a-gt> }
        # deindent closer token(s) when after cursor
        try %{ execute-keys -draft x <a-k> ^\h*[\]\)] <ret> gh / [\]\)] <ret> m <a-S> 1<a-&> }
    }
}


}
