COQC=coqc -q -R ../../FRAP Frap

.PHONY: all
all: Imperative.vo Hoare.vo Examples.vo Proofs.vo

%.vo : %.v
	$(COQC) $<

clean:
	rm *.vo *.aux *.glob -rf
