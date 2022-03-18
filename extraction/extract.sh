(cd ../theories; coqtop `cat _CoqProject` -l Dep/Extraction <<< "Quit." 2> /dev/null) | grep -Pzo "(?s)\(\* Extraction start \*\).*" | tr "\0" "\n" > dep.ml
(cd ../theories; coqtop `cat _CoqProject` -l NonDep/Extraction <<< "Quit." 2> /dev/null) | grep -Pzo "(?s)\(\* Extraction start \*\).*" | tr "\0" "\n" > non_dep.ml
