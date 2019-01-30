COQC=coqc -q -R ../../FRAP Frap

.PHONY: dependencies
dependencies: binary_tree_helpers.vo

.PHONY: all
all: binary_tree.vo

%.vo : %.v
	$(COQC) $<

clean:
	rm *.vo *.aux *.glob -rf
