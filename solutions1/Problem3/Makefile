COQC=coqc -q -R ../../FRAP Frap

.PHONY: dependencies
dependencies: Modeling.vo Problem.vo

%.vo : %.v
	$(COQC) $<

.PHONY: check
check: dependencies Solution.vo Check.vo

clean:
	rm *.vo *.aux *.glob -rf
