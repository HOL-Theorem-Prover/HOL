$| = 1;
$indent = 2;
print " ";
while (<>) {
  chomp;
  if (m|^Working in directory /tmp/hol98/src/(.*)$|) {
    $toprint = $1;
    if (length($toprint) + $indent + 1 > 75) {
      print "\n  $toprint";
      $indent = 2 + length($toprint);
    } else {
      print " $toprint";
      $indent += (length($toprint) + 1);
    }
  }
}
print "\n";
