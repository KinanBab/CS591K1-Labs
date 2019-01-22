COQC=coqc -q -R ../../FRAP Frap

.PHONY: all
all: intro_functional.vo binary_tree.vo

intro_functional.vo: intro_functional.v
	$(COQC) intro_functional

binary_tree.vo: binary_tree_helpers.vo binary_tree.v
	$(COQC) binary_tree

binary_tree_helpers.vo: binary_tree_helpers.v
	$(COQC) binary_tree_helpers

clean:
	rm *.vo *.aux *.glob -rf
