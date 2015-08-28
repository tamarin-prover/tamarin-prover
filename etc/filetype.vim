" autocommand to detect .spthy files
augroup filetypedetect
au BufNewFile,BufRead *.spthy	setf spthy
augroup END
