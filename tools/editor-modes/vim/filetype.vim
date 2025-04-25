augroup filetypedetect
  au BufRead,BufNewFile *.sml let maplocalleader = "h" | source /Users/binghe/ML/HOL.k15/tools/editor-modes/vim/hol.vim
  au BufRead,BufNewFile *?Script.sml setlocal filetype=hol4script
  " recognise pre-munger files as latex source
  au BufRead,BufNewFile *.htex setlocal filetype=htex syntax=tex
  "Uncomment the line below to automatically load Unicode
  "au BufRead,BufNewFile *?Script.sml source /Users/binghe/ML/HOL.k15/tools/editor-modes/vim/holabs.vim
  "Uncomment the line below to fold proofs
  "au BufRead,BufNewFile *?Script.sml setlocal foldmethod=syntax foldnestmax=1
augroup END
