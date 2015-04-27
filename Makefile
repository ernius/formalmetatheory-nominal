# name of agda compiler name
AGDA = agda2.4.2.2  

LATEX = pdflatex

# agda library location
AGDALIBRARYFLAGS = -i . -i ~/Documents/NewAgda/agda-stdlib-0.9/src/

# agda html
AGDAHTMLFLAGS = --html

# agda latex
AGDALATEXFLAGS = --latex

latex/%.tex : %.lagda
	$(AGDA) $(AGDALATEXFLAGS) $(AGDALIBRARYFLAGS) $<

bib : latex/resumen.bib
	cd latex; pdflatex resumen.tex; bibtex resumen;pdflatex resumen.tex;pdflatex resumen.tex; cd ..;

resumen : latex/resumen.tex latex/Substitution.tex latex/FreeVariables.tex latex/Atom.tex latex/Alpha.tex latex/Chi.tex latex/Equivariant.tex latex/ListProperties.tex latex/NaturalProperties.tex latex/Permutation.tex latex/TermAcc.tex latex/Term.tex latex/TermInduction.tex latex/TermRecursion.tex latex/Norrish.tex 
	cd latex; $(LATEX) resumen.tex; cd ..;	

Substitution : Substitution.lagda
	$(AGDA) $(AGDALIBRARYFLAGS) Substitution.lagda

FreeVariables : FreeVariables.lagda
	$(AGDA) $(AGDALIBRARYFLAGS) Substitution.lagda

html : *.lagda
	$(AGDA) $(AGDAHTMLFLAGS) $(AGDALIBRARYFLAGS) Substitution.lagda; cp -rf html/ ../gh-pages/formalmetatheory-nominal/

clean :
	rm *.agdai
