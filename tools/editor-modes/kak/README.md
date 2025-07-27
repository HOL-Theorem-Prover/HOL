# hol.kak

This is a HOL mode for Kakoune. Install by placing this somewhere in the autoload directory in your config. Beware the issue with a [local config autoload](https://github.com/mawww/kakoune/issues/554); if you haven't set up a proper config with autoload yet, you probably want to symlink the `share/kak/autoload` to your local autoload.

The plugin only supplies commands with the prefix `hol-`; there are no default keybinds, but I may eventually pick some. For now that can be up to you. Clippy will explain to you roughly what every command does, which should be familiar if you have used a HOL mode in one of the other supported editors before.

Before starting a session, you should make sure that `$HOLDIR` is set. You may start a HOL session by running `hol-start`, which will open a new terminal window which `hol.kak` will interface with through its other commands.

Starting a session sets up a hook to load theory dependencies on opening a new file, but does not load dependencies for files you already have open. You can force a load by running `hol-load-deps-current` on your open file.

There is no sanitisation of tactics yet, so sending tactics with dangling infix operators (e.g. `>>`) or mismatched brackets will fail.

## Nix-specific

This plugin behaves just like other kak plugins in nixpkgs. Call the package with the same pattern as in `default.nix` and use it e.g. in the plugins config for kak in home manager, which will automatically adjust autoload.
