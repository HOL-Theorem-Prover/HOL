#!/bin/bash
case $REQUEST_METHOD in
'POST')
export PATH="$HOME/bin:$PATH"
echo "Content-type: text/plain"
echo
cat | sed '0,/^\s*$/d' | tr -d '\r' | holqbf
;;
'GET')
echo "Content-type: text/html"
echo
cat <<EOF
<!doctype html>
<html>
<body>
<form method="post" enctype="multipart/form-data" action="holqbf.cgi">
<p><label><textarea name="article"></textarea></label></p>
<p><button>Submit</button></p>
</form>
</body>
</html>
EOF
;;
*)
echo "Content-type: text/plain"
echo
echo "Bad request method: $REQUEST_METHOD"
esac
