COQC=coqc -q -R ../../FRAP Frap

.PHONY: all
all: binary_tree.vo

binary_tree.vo: binary_tree_helpers.vo binary_tree.v
	$(COQC) binary_tree

binary_tree_helpers.vo: binary_tree_helpers.v
	$(COQC) binary_tree_helpers

clean:
	rm *.vo *.aux *.glob -rf
