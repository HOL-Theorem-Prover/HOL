#!/usr/bin/env python

import argparse


# Read arguments

parser = argparse.ArgumentParser(description='Decompile an ELF file.')
parser.add_argument('filename', metavar='filename', type=str,
                   help='base of filename, e.g. loop for loop.elf.txt')
parser.add_argument('--fast', dest='fast', action='store_const',
                   const=True, default=False,
                   help='fast mode skips some proofs')
parser.add_argument('--ignore', metavar='names', type=str, nargs='?',
                   default='',
                   help='comma separated list of function names that are to be ignored (decompiler output will contain stubs for these)')

args = parser.parse_args()

if args.fast:
  fast_str = 'true'
else:
  fast_str = 'false'


# Run HOL

import subprocess
import io
import sys
import os

def call_input_output(args,input_str,output_file):
  with open('.input.txt',"w") as input:
    input.write(input_str)
    input.close()
  with open('.input.txt',"r") as input, open(output_file,"wb") as out:
    try:
      ret = subprocess.call(args, stdin=input, stdout=out, stderr=out, universal_newlines=True, shell=True)
    except KeyboardInterrupt:
      print '\nInterrupted'
      exit(1)
    return ret

elf = os.path.abspath(args.filename)
output_file = os.path.abspath(args.filename + '_output.txt')

ml_input = """
use "writerLib"; load "decompileLib";
val _ = decompileLib.decomp "{0}" {1} "{2}";
"""

ml_input = ml_input.format(elf, fast_str, args.ignore)

decompiler_dir = os.path.dirname(sys.argv[0])
if decompiler_dir:
  os.chdir(decompiler_dir)

print "Building dependancies ...",
sys.stdout.flush()
ret = call_input_output('Holmake','','hol_output.txt')
if ret != 0:
  print "failed!"
  print "Holmake failed, abandoning."
  print "Short failure summary:"
  outp = os.path.abspath('hol_output.txt')
  last_lines = list (open (outp))[-20:]
  for l in ['\n'] + last_lines + ['\n']:
    print l,
  print "(more error information in %s )." % outp
  exit(1)
print "done."
sys.stdout.flush()

print "Decompiling {0} ... (output in {1})".format(elf,output_file),
sys.stdout.flush()
call_input_output('./local-hol-heap',ml_input,output_file)
last_lines = list (open (output_file))[-20:]
summaries = [i for (i, l) in enumerate (last_lines) if l.strip() == 'Summary']
if not summaries:
  print "failed!"
  print
  print "Short failure summary:"
  for l in ['\n'] + last_lines + ['\n']:
    print l,
  print "(more information in %s )" % output_file
  exit(1)
print "done."
for l in [''] + last_lines[summaries[-1]:]:
  print l,
sys.stdout.flush()
