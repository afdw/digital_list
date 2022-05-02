.PHONY: build clean

build:
	pdflatex main.tex
	biber main
	pdflatex main.tex
	pdflatex main.tex

clean:
	rm -f main.aux main.bbl main.bcf main.blg main.fdb_latexmk main.fls main.log main.out main.run.xml main.synctex.gz
