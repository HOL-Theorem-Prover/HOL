#!/usr/bin/env python3

# holwrap: it's like rlwrap but more colourful.
# Featuring some StandardML syntax highlighting, history and multiline input.
# Currently does print hol output until the next prompt (">") is read,
#   if you know how to fix this please make issue or PR on github.

# You will need python3 to run holwrap
# holwrap also depends on prompt_toolkit, pexpect and pygments, installable with pip,
#   e.g., pip3 install prompt_toolkit, pexpect
# Usage: ./holwrap.py hol <hol flags>
#   or: python3 holwrap.py hol <hol flags>
#   you could also substitute hol.bare or something here if you wanted.
# If hol is not in your path you will need to write the full path instead.
#   e.g., python3 holwrap.py /path/to/HOL/bin/hol

import sys, pexpect, re
from pygments.lexers.ml import SMLLexer
from prompt_toolkit import PromptSession
from prompt_toolkit.lexers import PygmentsLexer
from prompt_toolkit.history import FileHistory
from prompt_toolkit.auto_suggest import AutoSuggestFromHistory
from prompt_toolkit.key_binding import KeyBindings
from prompt_toolkit.filters import Condition
from prompt_toolkit.patch_stdout import patch_stdout
from prompt_toolkit.application import get_app

@Condition
def statement_ended():
    t = get_app().current_buffer.text
    return re.search("(;|^)\s*$",t) or re.search("(^|\n)(QED|End)\s*$",t)

bindings = KeyBindings()

@bindings.add(
    "enter",
    filter=statement_ended,
)
def _(event):
    event.current_buffer.validate_and_handle()

def main(argv):
    args =" ".join(argv[1:]) # this should be hol and flags for hol
    repl = pexpect.spawn(args, encoding='utf-8', echo=False, timeout=None)

    def find_prompt():
        # searches the output of hol for a prompt ">"
        return repl.expect_list(map(re.compile,["(\s+|^)>\s*$"]))#,"#\s*$"]))

    find_prompt()
    print(repl.before) # prints everything read from stout until the prompt
    repl.sendline("Parse.current_backend := PPBackEnd.vt100_terminal;")
    # for coloured hol terms TODO: make config option
    find_prompt()

    session = PromptSession("> ",
        lexer=PygmentsLexer(SMLLexer),
        history=FileHistory('.holwrap_history'),
        auto_suggest=AutoSuggestFromHistory(),
        multiline=True, # TODO make config option
        key_bindings=bindings # TODO add some useful keybindings?
        )

    while True:
        try:
            with patch_stdout():
                # prompt for input
                text = session.prompt()
            if text and text != "\n":
                repl.sendline(text.strip())
                # send input to hol
                find_prompt()
                print(repl.before) # print output after finding next prompt
        except pexpect.EOF:
            break # quit
        except EOFError:
            break # quit
        except KeyboardInterrupt:
            repl.sendcontrol('c')
            find_prompt()
            print(repl.before)
            continue
        except pexpect.TIMEOUT:
            # Timeout currently not set, this shouldn't happen unless changed
            repl.sendcontrol('c')
            print("Timeout reached")
            find_prompt()
            print(repl.before)
            continue
    repl.close(True) # close hol before exit

if __name__ == "__main__":
    main(sys.argv)
