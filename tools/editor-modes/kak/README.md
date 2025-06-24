# hol.kak

This is a HOL mode for Kakoune. It depends on the Kakoune [`repl` interface](https://github.com/mawww/kakoune/tree/master/rc/windowing/repl) which itself requires a multiplexer of sorts, like tmux or kitty (untested). You must be running kak in tmux.

Install by placing this somewhere in the autoload directory in your config. Beware the issue with a [local config autoload](https://github.com/mawww/kakoune/issues/554); if you haven't set up a proper config with autoload yet, you probably want to symlink the `share/kak/autoload` to your local autoload.

The plugin only supplies commands with the prefix `hol-`; there are no default keybinds, but I may eventually pick some. For now that can be up to you. Clippy will explain to you roughly what every command does, which should be familiar if you have used a HOL mode in one of the other supported editors before.

Starting a session sets up a hook to load theory dependencies on opening a new file, but does not load dependencies for files you already have open. You can force a load by running `hol-load-deps-current` on your open file.

There is no sanitisation at all right now, so `Definitions` must be `End`ed, tactics can't have loose operators, etc. You will probably also make sure to send in semicolons `;` after ML syntax. Note that you can just send an `End` or `;` after you have already sent something and that will just complete it.

When starting the HOL session with tmux, the focus shifts to the HOL session and you need to shift it back to kak. You can do this by typing the tmux leader (default `C+b`) then left, or probably `h` works too. I don't know how to keep the focus yet, but maybe there is a way.

## Nix-specific

This plugin behaves just like other kak plugins in nixpkgs. Call the package with the same pattern as in `default.nix` and use it e.g. in the plugins config for kak in home manager, which will automatically adjust autoload.
