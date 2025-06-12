define-command hol-start -docstring '
hol-start: start HOL instance in new tmux pane, from HOLDIR' %{
    evaluate-commands %{
        repl-new;
        repl-send-text %sh{printf "$HOLDIR/bin/hol --zero\n "};
        hook global BufOpenFile .*\.sml hol-load-deps-current
    }
}

define-command hol-send -docstring '
hol-send: send selection verbatim to HOL' %{
    evaluate-commands %{repl-send-text %sh{printf "%s\n\0 " "$kak_selection"}}
}

define-command hol-goal-send -docstring '
hol-goal-send: send selection as new goal to HOL' %{
    evaluate-commands %{repl-send-text %sh{printf "g(\`%s\`);\n\0 " "$kak_selection"}}
}

define-command hol-tactic -docstring '
hol-tactic: send selection as tactic to HOL' %{
    evaluate-commands %{repl-send-text %sh{printf "e(%s);\n\0 " "$kak_selection"}}
}

define-command hol-show-goal -docstring '
hol-show-goal: show current goal in HOL' %{
    evaluate-commands %{repl-send-text %sh{printf "p();\n\0 "}}
}

define-command hol-backup -docstring '
hol-backup: step back in proof in HOL' %{
    evaluate-commands %{repl-send-text %sh{printf "b();\n\0 "}}
}

define-command hol-drop -docstring '
hol-drop: drop goal in HOL' %{
    evaluate-commands %{repl-send-text %sh{printf "drop();\n\0 "}}
}

define-command hol-rotate -docstring '
hol-rotate <n>: rotate subgoals n times in HOL' -params 1 %{
    evaluate-commands %{repl-send-text %sh{printf "r $1;\n\0 "}}
}

define-command hol-restart-proof -docstring '
hol-restart-proof: restart proof in HOL' %{
    evaluate-commands %{repl-send-text %sh{printf "restart();\n\0 "}}
}

define-command hol-load-deps-for -docstring '
hol-load-deps-for: load dependencies for a HOL file' -params 1 %{
    evaluate-commands %{repl-send-text %sh{$HOLDIR/bin/holdeptool.exe $1 | sed 's/.*/qload "&" handle _ => (); /'}}
}

define-command hol-load-deps-current -docstring '
hol-load-deps-current: load dependencies for current buffer HOL file' %{hol-load-deps-for %val{buffile}}
