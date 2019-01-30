COQC=coqc -q -R ../../FRAP Frap

.PHONY: all
all: intro_functional.vo

%.vo : %.v
	$(COQC) $<

clean:
	rm *.vo *.aux *.glob -rf
