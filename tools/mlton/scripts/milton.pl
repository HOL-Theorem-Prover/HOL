#!/usr/bin/perl -w

use IO::Handle;
STDOUT->autoflush(1);

sub mblock {
    foreach $file (@_) {
        print "\n(*#line 0.0 \"$file\"*)\n";
        system "cat $file | ../../bin/unquote";
        print STDERR ".";
    }
}

(0 < scalar(@ARGV)) or die "Usage: $0 file.sml ...";

print STDERR "preparing sml files for mlton";

mblock @ARGV;

print STDERR "\n";
