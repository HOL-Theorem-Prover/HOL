#!/usr/bin/env python

import random
import sys
import string

size = int(sys.argv[1])
s = sys.argv[2]

for i in xrange(size):
    sys.stdout.write(random.choice(s)) #string.printable
