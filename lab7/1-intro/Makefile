all: intro.dats
	patscc -o intro intro.dats

z3: intro.dats
	patsopt -tc --constraint-export -d intro.dats | patsolve_z3 -i -
	patscc --constraint-ignore -o intro intro.dats
