#!/usr/bin/perl
(@ARGV == 2) || die "Usage: compare.pl file1 file2";

($file1, $file2) = @ARGV;

open(FILE1, $file1) || die "Couldn't open $file1";

while (<FILE1>) {
  chomp;
  split;
  $file1_hash{$_[0]} = $_[2] if ($_[1] eq "OK");
}

close(FILE1);

open(FILE2, $file2) || die "Couldn't open $file2";

while (<FILE2>) {
  chomp;
  split;
  $file2_hash{$_[0]} = $_[2] if ($_[1] eq "OK");
}

close(FILE2);

$accum_absolute = 0;
$accum_percent = 0;

$accum_file1 = 0;
$accum_file2 = 0;

$zero_worseners = 0;
$biggest_worsening = 0;
$biggest_improvement = 0;

@keys = sort(keys(%file1_hash));

foreach (@keys) {
  $file1 = $file1_hash{$_};
  $file2 = $file2_hash{$_};
  next if (!defined $file2) ;
  $accum_file1 += $file1;
  $accum_file2 += $file2;
  $absolute_improvement = $file1 - $file2;
  if ($absolute_improvement >= 0) {
    if ($absolute_improvement > $biggest_improvement) {
      $biggest_improvement = $absolute_improvement;
      $best = $_;
    }
  } else {
    if ($absolute_improvement < $biggest_worsening) {
      $biggest_worsening = $absolute_improvement;
      $worst = $_;
    }
  }
  $percent_improvement =
    (defined $file2 && $file2 != 0.0) ? $absolute_improvement / $file2 : 0;
  printf "%-30s %8.3f %8.3f %8.3f %5.2f\n", $_, $file1, $file2,
    $absolute_improvement, $percent_improvement;
  $accum_absolute += $absolute_improvement;
  $accum_percent += $percent_improvement;
  if ($file1 == 0.0) { $zero_worseners += $file2; }
}
$count = @keys;
printf "Total time in file1: %6.3f\n", $accum_file1;
printf "Total time in file2: %6.3f\n", $accum_file2;
printf "Absolute improvement: %6.3f\n", $accum_absolute;
printf "Average improvement: %6.3f\n", $accum_absolute / $count;
printf "Biggest worsening: %6.3f (by %s)\n", $biggest_worsening, $worst;
printf "Biggest improvement: %6.3f (by %s)\n", $biggest_improvement, $best;
printf "Average percent improvement: %6.3f\n", ($accum_percent / $count);
printf "Zero worseners: %6.3f\n", $zero_worseners;

