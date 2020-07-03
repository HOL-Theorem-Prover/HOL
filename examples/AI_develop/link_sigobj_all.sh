for FILE in $(ls *.sig); do
  sh link_sigobj.sh $FILE
done
