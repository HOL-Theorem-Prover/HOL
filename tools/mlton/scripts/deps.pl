#!/usr/bin/perl -w

use IO::Handle;
STDOUT->autoflush(1);

sub avoid_dir {
    (scalar @_ == 1) or die;
    my ($dir) = @_;

    return ($dir =~ /muddy.?$/ or
            $dir =~ /\/temporal\// or
            $dir =~ /HolBdd$/);
}

sub src_dirs {
    @dirs = ("../../src/portableML", "../../src/experimental-kernel");
    open BUILDFILE, "$BUILD_FILE";
    while ($line = <BUILDFILE>) {
        chomp $line;
        
        $line =~ s/ *\#.*$//;
        $line =~ s/^ +//;

        ($line !~ / /) or die;

        ($line ne "") or next;

        $dir = "../../$line";

        if (avoid_dir $dir) { next; }

        push @dirs, $dir;
    }
    close BUILDFILE;
}

sub avoid_file {
    (scalar @_ == 1) or die;
    my ($file) = @_;

    return ($file =~ /selftest(\.sml)?$/ or
            $file =~ /holmake_interactive(\.sml)?$/ or
            $file =~ /mkword(\.sml)?$/ or
            $file =~ /Script(\.sml)?$/);
}

sub check {
    (scalar @_ == 2) or die;
    my ($dir,$file) = @_;

    if ($file =~ /\.sig$/) {
        if (system ("grep signature $dir/$file >/dev/null") != 0) {
            warn "deps.pl: no \"signature\" in file $dir/$file\n";
        }
    }
    elsif ($file =~ /\.sml$/) {
        if (system ("grep structure $dir/$file >/dev/null") != 0) {
            warn "deps.pl: no \"structure\" in file $dir/$file\n";
        }
    }
    else {
        warn "deps.pl: strange filename $dir/$file\n";
    }
}

sub rewrite {
    (scalar @_ == 2) or die;
    my ($dir,$file) = @_;

#    check $dir,$file;
    
    $f = $file;

    if (-f "src/$file") { $r = "src/$file"; }
    elsif (-f "$dir/$f") { $r = "$dir/$f"; }
    else { die "deps.pl: no matching file for $dir/$file\n"; }

    if ($r ne "$dir/$file") { print STDERR "  $dir/$file -> $r\n"; }

    return $r;
}

sub process_files {
    (scalar @_ == 1) or die;
    my ($dir) = @_;

    (-d "$dir/.HOLMK") or return;

    %files = ();
    open FILES, "(cd $dir ; ls) |";
    while ($file = <FILES>) {
        chomp $file;

        (-f "$dir/$file") or next;
        $file =~ /\.sig$/ or $file =~ /\.sml$/ or next;
        if (avoid_file $file) { next; }
        
        $module = $file;
        $module =~ s/\.sml$// or $module =~ s/\.sig$// or die;

        $f = $files{$module};
        $files{$module} = (defined $f) ? ($f . " " . $file) : $file;
    }
    close FILES;

#    print STDOUT ("\n\n" . join (" ", keys %files) . "\n\n");

    %deps = ();
    $cmd = "cat $dir/.HOLMK/*" .
           ((-f "$dir/Holmakefile") ? " $dir/Holmakefile" : "");

    open DEPS, "$cmd |";
    while ($line = <DEPS>) {
        chomp $line;

        if ($line =~ /^([^.]*)(\.ui|\.uo): (.*)$/) {
            $target = $1;
            $deps = $3;

            if (avoid_file $target) { next; }
            (defined $files{$target}) or die "Unknown target: $target\n";

            foreach $dep (split (/ /, $deps)) {
                $dep =~ s/\.ui$// or $dep =~ s/\.uo$// or
                    $dep =~ s/\.sig$// or $dep =~ s/\.sml$// or
                        die "Dodgy dep for target $target: $dep\n";
                $d = $deps{$target};
                $deps{$target} = (defined $d) ? ($d . " " . $dep) : $dep;
            }
        }
    }
    close DEPS;

    while (0 < scalar (keys %files)) {
        foreach $module (sort { $a cmp $b; } keys %files) {
            $success = "true";
            if (defined $deps{$module}) {
                foreach $dep (split (/ /, $deps{$module})) {
                    if ($dep eq $module) { next; }
                    
                    if (defined $files{$dep}) {
                        $success = "false";
#                        print STDOUT "$module <- $dep\n";
                        last;
                    }
                }
            }
            if ($success eq "true") {
                print STDOUT " \\\n ";
                foreach $file (split (/ /, $files{$module})) {
                    $f = rewrite $dir,$file;
                    print STDOUT " $f";
                }
                delete $files{$module};
            }
        }
    }
}

sub process_dirs {
    print STDOUT "$name =";
    foreach $dir (@dirs) { print STDERR "$dir\n"; process_files $dir; }
    print STDOUT "\n";
}

$BUILD_FILE = "../../tools/build-sequence";

if (scalar @ARGV == 0) {
    $name = "SRC";
    src_dirs ();
}
else {
    $name = shift @ARGV;
    @dirs = @ARGV;
}

process_dirs ();
