#!/usr/bin/perl

use IO::Handle;
STDOUT->autoflush(1);

sub unquotify {
    if (scalar @quotes == 0) { return; }

    $pre = "[";

    for $quote (@quotes) {
        $nl = chomp $quote;
        @qs = split (/\^(\w+)/, $quote);
        @ps = ();

        for ($s = 0; 0 < scalar @qs; $s = 1 - $s) {
            $q = shift @qs;
            if ($s == 0) {
                $q =~ s/\\/\\\\/g;
                $q =~ s/\"/\\\"/g;
                push @ps, "QUOTE \"$q\"" unless ($q eq "");
            }
            elsif ($s == 1) {
                push @ps, "ANTIQUOTE $q";
            }
            else { die; }
        }

        if (0 < $nl) {
            if (0 < scalar @ps) {
                $p = pop @ps;
                if ($p =~ /QUOTE \"(.*)\"/) { push @ps, "QUOTE \"$1\\n\""; }
                else { push @ps, $p; push @ps, "QUOTE \"\\n\""; }
            }
            else { push @ps, "QUOTE \"\\n\""; }
        }
        else {
            (0 < scalar @ps) or die;
        }

        print ($pre . join (", ", @ps));
        $pre = ",\n";
    }

    print "]";

    @quotes = ();
}

$PROG = "mosml2mlton.pl";
$state = "normal";
$comment = 0;

(scalar(@ARGV) == 0) or die "usage: $PROG <mosmlfile.sml >mltonfile.sml";

while ($line = <STDIN>) {
    (chomp ($line) == 1)
        or warn "$PROG: no terminating newline\nline = '$line'\n";

    $line =~ s/General\.//g;

    while (1) {
        if ($state eq "quote") {
            if ($line =~ /(.*?)\`(.*)$/) {
                push @quotes, $1;
                $line = $2;
                unquotify ();
                $state = "normal";
            }
            else {
                push @quotes, "$line\n";
                last;
            }
        }
        elsif ($line =~ /^(.*?)(\`|\(\*|\*\)|\")(.*)$/) {
            $leadup = $1;
            $pat = $2;
            $line = $3;
            print $leadup;

            print $pat unless ($pat eq "`");

            if ($pat eq "`") {
                if ($state eq "normal") { $state = "quote"; }
                else { print "`"; }
            }
            elsif ($pat eq "(*") {
                if ($state eq "normal") { $state = "comment"; }
                elsif ($state eq "comment") { ++$comment; }
                else {
                    ($state eq "dquote") or die;
                }
            }
            elsif ($pat eq "*)") {
                if ($state eq "comment") {
                    if ($comment == 0) { $state = "normal"; }
                    else { --$comment; }
                }
                else {
                    ($state eq "dquote") or die "misplaced *)\n";
                }
            }
            elsif ($pat eq "\"") {
                if ($state eq "normal" or $state eq "dquote") {
                    $leadup =~ /(\\*)$/;
                    $escapes = $1;
                    $escapes =~ s/\\\\//g;
                    if ($escapes eq "") {
                        if ($state eq "normal") { $state = "dquote"; }
                        elsif ($state eq "dquote") { $state = "normal"; }
                        else { die; }
                    }
                    else {
                        ($escapes eq "\\") or die;
                        ($state eq "dquote") or die;
                    }
                }
            }
            else {
                die;
            }
        }
        else {
            print "$line\n";
            last;
        }
    }
}

if ($state eq "quote") {
    warn "$PROG: EOF inside \` quote\n";
}
elsif ($state eq "dquote") {
    warn "$PROG: EOF inside \" quote\n";
}
elsif ($state eq "comment") {
    warn "$PROG: EOF inside comment\n";
}
else {
    ($state eq "normal") or die;
}
