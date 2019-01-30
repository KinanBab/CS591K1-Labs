COQC=coqc -q -R ../../FRAP Frap

.PHONE: dependencies
dependencies: Helpers.vo Problem.vo

%.vo : %.v
	$(COQC) $<

.PHONY: check
check: dependencies Solution.vo
	$(COQC) Check

clean:
	rm *.vo *.aux *.glob -rf
