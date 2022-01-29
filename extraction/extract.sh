(cd ../theories; coqtop `cat _CoqProject` -l Extraction <<< "Quit." 2> /dev/null) | grep -Pzo "(?s)\(\* Extraction start \*\).*" | tr "\0" "\n" > digital_list.ml
