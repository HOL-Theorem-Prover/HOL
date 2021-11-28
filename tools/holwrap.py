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

# Due to the mutiline input, holwrap won't send input until it sees a semicolon,
#  'QED' or 'End'. You can force it with Esc-Enter, but it could cause problems.

import sys, pexpect, re
from time import ctime
from os import remove
from argparse import ArgumentParser
from pygments.lexers.ml import SMLLexer
from prompt_toolkit import PromptSession, prompt
from prompt_toolkit.lexers import PygmentsLexer
from prompt_toolkit.history import FileHistory, InMemoryHistory
from prompt_toolkit.auto_suggest import AutoSuggestFromHistory
from prompt_toolkit.key_binding import KeyBindings
from prompt_toolkit.filters import Condition
from prompt_toolkit.patch_stdout import patch_stdout
from prompt_toolkit.application import get_app

class Tee:
    def __init__(self, file1, file2=sys.stdout):
        self.file1 = file1
        self.file2 = file2
    def write(self, data):
        self.file1.write(data)
        self.file2.write(data)
    def flush(self):
        self.file1.flush()
        self.file2.flush()

multiline_validator = re.compile(r'(?:;|^QED|^End)\s*$', re.MULTILINE)
# for multiline TODO: do not validate the input or send at each line end
@Condition
def statement_ended():
    return multiline_validator.search(get_app().current_buffer.text)

bindings = KeyBindings()

@bindings.add(
    "enter",
    filter=statement_ended,
) # TODO add some useful keybindings?
def _(event):
    event.current_buffer.validate_and_handle()

def main(cmd, args=[],
  log_file=None, history_file='.holwrap_history',
  unicode=False, backend='PPBackEnd.vt100_terminal', 
  multiline=True, prompt_string="'> "):
    # multiline=False is not supported
    if log_file:
        log_file.write(f'New session on {ctime()}\r\n')
    log_output = Tee(log_file) if log_file else sys.stdout

    # initialissation script to prepare hol for holwrap
    init_file = '.holwrap.sml'
    init_begin = 'BEGIN-INIT'
    init_end = 'END-INIT'
    with open(init_file, 'w') as cf:
        cf.write('\n'.join([f'print "{init_begin}";',
            f'set_trace "Unicode" {int(unicode)};',
            'PolyML.Compiler.prompt1:= "{}";'.format(prompt_string.replace('"', '\\"')),
            'PolyML.Compiler.prompt2:= "";', # Prevent extraneous prompt strings to appear in multiline mode
            f'Parse.current_backend:= {backend};',
            f'print "{init_end}";']))
    args.insert(0, init_file)
    repl = pexpect.spawn(cmd, args, encoding='utf-8', echo=False, timeout=None)
    repl.expect_exact(init_begin)
    # logging is off expect for welcome message, the user doesn't need to know what configuration is done
    log_output.write(repl.before)
    repl.expect_exact(init_end)
    remove(init_file)
    del init_file, init_begin, init_end

    # log everything to the log file but do not echo to stdout the user input
    repl.logfile_read = log_output
    repl.logfile_send = log_file
    if repl.expect_exact([prompt_string, pexpect.EOF])!=0:
        # probably an initialisation error, may happend when giving a file to hol
        print(f'{cmd} exited. Terminating holwrap session.')
        return

    # main prompt, help prompt
    prompts = [prompt_string, ' quit: ']
    session = PromptSession('> ',
        prompt_continuation='# ',
        lexer=PygmentsLexer(SMLLexer),
        # no history file still stores an history in memory
        history=FileHistory(history_file) if history_file else InMemoryHistory(),
        auto_suggest=AutoSuggestFromHistory(),
        multiline=multiline,
        key_bindings=bindings)

    while True:
        try:
            print('\r', end='') # Fix double prompt
            text = session.prompt()
            repl.sendline(text)
            while repl.expect_exact(prompts)==1: # help prompt, no multiline makes it way easier
                text = prompt()
                repl.sendline(text)
        except pexpect.EOF: # End of process's output
            break
        except EOFError: # End of user's input
            repl.logfile_send = None # Do not record further inputs, session is ended
            repl.sendeof()
            repl.expect_exact([pexpect.EOF, pexpect.TIMEOUT], timeout=5) # wait for termination or force it
            if log_file:
                log_file.write('\r\n') # nicer end of log
            break
        except KeyboardInterrupt:
            repl.sendcontrol('c')
            repl.expect_exact(prompt_string)
            continue
        except pexpect.TIMEOUT:
            # Timeout currently not set, this shouldn't happen unless changed
            repl.sendcontrol('c')
            print("Timeout reached")
            repl.expect_exact(prompt_string)
            continue
    repl.close(True) # Force hol to close if it is still alive
    if log_file:
        log_file.write('Session ended\r\n\r\n')

if __name__ == "__main__":
    parser = ArgumentParser(description='Wrapper arround hol input, like rlwrap but with syntax highlighting.',
        epilog='The double dash argument `--` must be used once before any hol dashed argument.',
        allow_abbrev=False)
    parser.add_argument('--log-file', '-l',
        default='.holwrap_log',
        help='File to log all inputs and outputs.')
    parser.add_argument('--no-log', dest='log_file',
        action='store_const', const=None,
        help='Do not generate a log file.')
    parser.add_argument('--history-file', '-H',
        default='.holwrap_history',
        help='File to store the input history.')
    parser.add_argument('--no-history',
        dest='history_file', action='store_const', const=None,
        help='Do not store the history in a file.')
    parser.add_argument('--backend',
        default='PPBackEnd.vt100_terminal',
        help='Hol command to set terminal kind, do not use unless you know what you are doing!')
    parser.add_argument('--utf-8', '-u',
        action='store_true', default=True,
        help='Set hol output to utf-8 (default).')
    parser.add_argument('--ascii', '-a',
        dest='utf_8', action='store_false',
        help='Set hol output to ascii.')
    parser.add_argument('--multi-line',
        action='store_true', default=True,
        help='Use multiline input (default).')
#    parser.add_argument('--single-line',
#        dest='multi_line', action='store_false',
#        help='Do not use, WIP.')
    parser.add_argument('--prompt-string',
        default="'> ",
        help='Set hol prompt string to something that would never be printed in other circumstances.')
    parser.add_argument('hol_path', help='hol executable path.')
    parser.add_argument('hol_args', nargs='*', help='hol arguments.')
    args = parser.parse_intermixed_args()
    del parser
    log_file = open(args.log_file, 'a', encoding='utf-8') if args.log_file else None
    try:
        main(args.hol_path, args=args.hol_args,
            log_file=log_file, history_file=args.history_file,
            backend=args.backend, unicode=args.utf_8,
            multiline=args.multi_line, prompt_string=args.prompt_string)
    finally:
        if log_file:
            log_file.close()
