augroup filetypedetect
  au BufRead,BufNewFile *.sml let maplocalleader = "h" | source /Users/josephchan/HOL/tools/vim/hol.vim
  " recognise pre-munger files as latex source
  au BufRead,BufNewFile *.htex setlocal filetype=htex syntax=tex
  "Uncomment the line below to automatically load Unicode
  "au BufRead,BufNewFile *?Script.sml source /Users/josephchan/HOL/tools/vim/holabs.vim
  "Uncomment the line below to fold proofs
  "au BufRead,BufNewFile *?Script.sml setlocal foldmethod=marker foldmarker=Proof,QED foldnestmax=1
augroup END
