COQC=coqc -q -R ../../FRAP Frap

.PHONY: all
all: reverse.vo sum_to.vo certified_programming.vo

%.vo : %.v
	$(COQC) $<

clean:
	rm *.vo *.aux *.glob -rf
