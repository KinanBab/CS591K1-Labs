z3: fact.dats
	patsopt -tc --constraint-export -d fact.dats | patsolve_z3 -i -
	patscc --constraint-ignore -o fact fact.dats
