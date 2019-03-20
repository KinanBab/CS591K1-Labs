props: props.dats
	patscc -o props props.dats
	
props-z3: props.dats
	patsopt -tc --constraint-export -d props.dats | patsolve_z3 -i -
	patscc --constraint-ignore -o props props.dats

bools: bools.dats
	patscc -o bools bools.dats

bools-z3: bools.dats
	patsopt -tc --constraint-export -d bools.dats | patsolve_z3 -i -
	patscc --constraint-ignore -o bools bools.dats

.PHONY: clean
clean:
	rm *.c -rf
	rm props -rf
	rm bools -rf
