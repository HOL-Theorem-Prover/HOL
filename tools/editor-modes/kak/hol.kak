hook global BufCreate .*Script\.sml %{
    set-option buffer filetype holscript
}

hook global WinSetOption filetype=holscript %{
    require-module hol
}

hook -group holscript-highlight global WinSetOption filetype=holscript %{
    add-highlighter window/ini ref holscript
    hook -once -always window WinSetOption filetype=.* %{ remove-highlighter window/holscript }
}

provide-module hol %{

declare-option str holfifo

define-command hol-start -docstring '
hol-start: start HOL instance in new terminal window, from HOLDIR' %{
    hook global BufOpenFile .*Script\.sml hol-load-deps-current
    evaluate-commands %sh{
        holfifo=$(mktemp -d /tmp/kak-fifo.XXXXXXXX)/fifo
        mkfifo $holfifo
        printf "set-option current holfifo '%s'" "$holfifo"
    }
    terminal sh -i -c %sh{
        printf "%s\n\n" "cat > $kak_opt_holfifo & $HOLDIR/bin/hol --zero < $kak_opt_holfifo"
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

}
