COQC=coqc -q -R ../../FRAP Frap

.PHONE: dependencies
dependencies: Helpers.vo Problem.vo

Helpers.vo: Helpers.v
	$(COQC) Helpers

Problem.vo: Problem.v
	$(COQC) Problem

Solution.vo: Solution.v
	$(COQC) Solution

.PHONY: check
check: dependencies Solution.vo
	$(COQC) Check

clean:
	rm *.vo *.aux *.glob -rf
