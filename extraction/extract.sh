(cd ..; coqtop -l DigitalList.v <<< "Quit." 2> /dev/null) | grep -Pzo "(?s)\(\* Extraction start \*\).*" | tr "\0" "\n" > digital_list.ml
