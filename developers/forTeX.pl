local $dropping = 0;

while (<>)
{
    if (m/\(\* remove output end \*\)/) {
        $dropping = 0;
        next;
    }
    next if $dropping;
    if (m/\(\* remove output begin \*\)/) {
        s/\(\* remove output begin \*\)/  .../;
        $dropping = 1;
    }
    s///g;
    s/\\/\\bs{}/g;
    s/∀/\\(\\forall\\)/g;
    s/∃/\\(\\exists\\)/g;
    s/⇔/\\(\\iff\\)/g;
    s/⇒/\\(\\Rightarrow\\)/g;
    s/¬/\\(\\neg\\)/g;
    s/∧/\\(\\land\\)/g;
    s/∨/\\(\\lor\\)/g;
    s/≤/\\(\\le\\)/g;
    s/^# /  /g;
    s/^> *$//g;
    print;
}
