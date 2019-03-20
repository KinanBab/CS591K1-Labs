build: list.dats
	patscc -o list list.dats

z3: list.dats
	patsopt -tc --constraint-export -d list.dats | patsolve_z3 -i -
	patscc --constraint-ignore -o list list.dats

clean:
	rm -rf *.c list
