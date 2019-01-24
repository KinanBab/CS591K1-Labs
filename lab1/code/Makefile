COQC=coqc -q -R ../../FRAP Frap

.PHONY: all
all: intro_functional.vo

intro_functional.vo: intro_functional.v
	$(COQC) intro_functional

clean:
	rm *.vo *.aux *.glob -rf
